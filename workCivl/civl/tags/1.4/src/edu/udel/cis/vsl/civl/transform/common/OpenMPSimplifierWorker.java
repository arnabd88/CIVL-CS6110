package edu.udel.cis.vsl.civl.transform.common;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.entity.IF.Entity;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.AttributeKey;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpForNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpParallelNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpReductionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpExecutableNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpSymbolReductionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpSyncNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpSyncNode.OmpSyncNodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpWorksharingNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpWorksharingNode.OmpWorksharingNodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.DeclarationListNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ForLoopInitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ForLoopNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.IfNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.LoopNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ReturnNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.SwitchNode;
import edu.udel.cis.vsl.abc.ast.util.ExpressionEvaluator;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;

/**
 * This transformer analyzes OpenMP constructs and converts them to simpler,
 * i.e., less concurrent, instances of constructs.
 * 
 * This transform operates in two phases:
 * 
 * 1) Analyze OpenMP workshares to determine those that are provably
 * thread-independent, i.e., execution of workshares in parallel is guaranteed
 * to compute the same result.
 * 
 * 2) Transform OpenMP constructs based on the analysis results.
 * 
 * TBD: a) support nowait clauses b) support collapse clauses (confirm whether
 * collapse uses variables or the first "k" row indices) c) what is the
 * semantics of a parallel region with no pragma, i.e., do we have to reason
 * about its independence to remove the parallel pragma d) intra-iteration
 * dependences, e.g., x[i] = x[i] + a; e) critical, barrier, master, single and
 * other workshares f) calling sensitive parallel workshare nesting, i.e.,
 * caller has parallel pragma, callee has workshare g) semantics of nowait for
 * that continues to method return h) treatment of omp_ calls, i.e., should we
 * preserve the parallelism since the calls likely depend on it i) detect
 * non-escaping heap data from within a omp pragma context, e.g.,
 * fig4.98-threadprivate.c j) default private/shared when there are explicit
 * shared/private clauses that don't mention the var
 * 
 * 
 * @author dwyer
 * 
 */
public class OpenMPSimplifierWorker extends BaseWorker {

	// TBD: clean this up
	private AttributeKey dependenceKey;

	// Visitor identifies scalars through their "defining" declaration
	private Set<Entity> writeVars;
	private Set<Entity> readVars;
	private Set<OperatorNode> writeArrayRefs;
	private Set<OperatorNode> readArrayRefs;
	
	private Set<Entity> sharedWrites;
	private Set<Entity> sharedReads;
	private Set<OperatorNode> sharedArrayWrites;
	private Set<OperatorNode> sharedArrayReads;

	private Set<Entity> ompMethods;
	private Set<FunctionDefinitionNode> ompMethodDefinitions;

	private boolean allIndependent;

	private List<Entity> privateIDs;
	private List<Entity> loopPrivateIDs;
	
	private boolean debug = false;

	public OpenMPSimplifierWorker(ASTFactory astFactory) {
		super("OpenMPSimplifier", astFactory);
		this.identifierPrefix = "$omp_sim_";
	}

	@Override
	public AST transform(AST unit) throws SyntaxException {
		SequenceNode<BlockItemNode> rootNode = unit.getRootNode();

		assert this.astFactory == unit.getASTFactory();
		assert this.nodeFactory == astFactory.getNodeFactory();
		unit.release();
		
		//OpenMPParallelRegions ompRegions = new OpenMPParallelRegions(rootNode);

		/*
		 * TBD: We want a proper inter-procedural analysis. This is more of a
		 * stop-gap.
		 * 
		 * There are two challenges: 1) Detect orphaning "omp parallel"
		 * statements - since they should not be simplified without considering
		 * whether the methods they call are themselves simplified 2) Detecting
		 * orphaned "omp" statements - since they should be analyzed for
		 * simplification even though they might not be lexically nested within
		 * an "omp parallel"
		 * 
		 * We collect the set of methods that contain an omp construct,
		 * recording their entities to detect calls to such methods for case 1)
		 * and recording their definition to drive analysis into those methods
		 * to handle case 2)
		 */
		ompMethods = new HashSet<Entity>();
		ompMethodDefinitions = new HashSet<FunctionDefinitionNode>();
		collectOmpMethods(rootNode);

		for (FunctionDefinitionNode fdn : ompMethodDefinitions) {
			transformOmp(fdn);
		}

		return astFactory.newAST(rootNode, unit.getSourceFiles());
	}

	AttributeKey getAttributeKey() {
		return this.dependenceKey;
	}

	private void addEntities(List<Entity> entityList,
			SequenceNode<IdentifierExpressionNode> clauseList) {
		if (clauseList != null) {
			for (IdentifierExpressionNode idExpression : clauseList) {
				Entity idEnt = idExpression.getIdentifier().getEntity();

				entityList.add(idEnt);
			}
		}
	}

	/*
	 * Scan program to collect methods involving omp constructs.
	 */
	private void collectOmpMethods(ASTNode node) {
		if (node instanceof FunctionDefinitionNode) {
			FunctionDefinitionNode fdn = (FunctionDefinitionNode) node;
			if (hasOmpConstruct(fdn.getBody())) {
				ompMethods.add(fdn.getEntity());
				ompMethodDefinitions.add(fdn);
			}
		} else if (node != null) {
			Iterable<ASTNode> children = node.children();
			for (ASTNode child : children) {
				collectOmpMethods(child);
			}
		}
	}

	private boolean callsMethodWithOmpConstruct(ASTNode node) {
		boolean result = false;
		if (node instanceof FunctionCallNode) {
			ExpressionNode fun = ((FunctionCallNode) node).getFunction();
			if (fun instanceof IdentifierExpressionNode) {
				result = ompMethods.contains(((IdentifierExpressionNode) fun)
						.getIdentifier().getEntity());
			}
		} else if (node != null) {
			Iterable<ASTNode> children = node.children();
			for (ASTNode child : children) {
				result = callsMethodWithOmpConstruct(child);
				if (result)
					break;
			}
		}
		return result;
	}

	/*
	 * Traverse the method declaration analyzing and simplifying omp constructs
	 */
	private void transformOmp(ASTNode node) {
		if (node instanceof OmpParallelNode) {
			OmpParallelNode opn = (OmpParallelNode) node;
			/*
			 * TBD: this code does not yet handle: - nested parallel blocks -
			 * sections workshares - collapse clauses - chunk clauses - omp_*
			 * calls which should be interpreted as being dependent
			 */

			/*
			 * Determine the private variables since they cannot generate
			 * dependences.
			 */
			privateIDs = new ArrayList<Entity>();
			addEntities(privateIDs, opn.privateList());
			addEntities(privateIDs, opn.copyinList());
			addEntities(privateIDs, opn.copyprivateList());
			addEntities(privateIDs, opn.firstprivateList());
			addEntities(privateIDs, opn.lastprivateList());
			SequenceNode<OmpReductionNode> reductionList = opn.reductionList();
			if (reductionList != null) {
				for (OmpReductionNode r : reductionList) {
					addEntities(privateIDs, r.variables());
				}
			}
			
			/*
			 * Initialize shared read/writes performed within parallel, but not in workshares
			 */
			sharedWrites = new HashSet<Entity>();
			sharedReads = new HashSet<Entity>();
			sharedArrayWrites = new HashSet<OperatorNode>();
			sharedArrayReads = new HashSet<OperatorNode>();

			/*
			 * Analyze the workshares contained lexically within the parallel
			 * node. A parallel node is "orphaned" if it makes calls to methods
			 * that contain OpenMP statements or calls. An orphaned parallel
			 * should not be removed without determining if all called methods
			 * can be simplified to eliminate their OpenMP statements.
			 * 
			 * TBD: Currently the orphan analysis only checks a single level of
			 * call; the full solution would require construction of a call
			 * graph.
			 */
			allIndependent = true;

			// Visit the rest of this node
			transformOmpWorkshare(opn.statementNode());
			
			/* Check for dependences between statements that are not within workshares */
			sharedWrites.retainAll(sharedReads);
			allIndependent &= sharedWrites.isEmpty();
			allIndependent &= noArrayRefDependences(sharedArrayWrites, sharedArrayReads);

			boolean isOrphaned = callsMethodWithOmpConstruct(opn
					.statementNode());

			if (allIndependent && !isOrphaned) {
				/*
				 * Remove the nested omp constructs, e.g., workshares, calls to
				 * omp_*, ordered sync nodes, etc.
				 */
				removeOmpConstruct(opn.statementNode());

				/*
				 * NB: the call above can change its argument (by restructuring
				 * the AST), so we need to recompute the statementNode below.
				 */				

				// Remove "statement" node from "omp parallel" node
				StatementNode stmt = opn.statementNode();
				int stmtIndex = getChildIndex(opn, stmt);
				assert stmtIndex != -1;
				opn.removeChild(stmtIndex);

				// Link "statement" into the "omp parallel" parent
				ASTNode parent = opn.parent();
				int parentIndex = getChildIndex(parent, opn);
				assert parentIndex != -1;
				parent.setChild(parentIndex, stmt);
			}

		} else if (node instanceof OmpExecutableNode) {
			privateIDs = new ArrayList<Entity>();

			transformOmpWorkshare(node);

		} else if (node != null) {
			// BUG: can get here with null values in parallelfor.c example

			/*
			 * Could match other types here that have no ForLoopNode below them
			 * and skip their traversal to speed things up.
			 */
			Iterable<ASTNode> children = node.children();
			for (ASTNode child : children) {
				transformOmp(child);
			}
		}
	}

	/*
	 * This method assumes that all of the OMP statements that are encountered
	 * can be safely removed or transformed into non-OMP equivalents.
	 */
	private void removeOmpConstruct(ASTNode node) {
		if (node instanceof OmpExecutableNode) {
			// Remove "statement" node from "omp statement" node
			StatementNode stmt = ((OmpExecutableNode) node).statementNode();
			int stmtIndex = getChildIndex(node, stmt);
			assert stmtIndex != -1;
			node.removeChild(stmtIndex);

			// Link "statement" into the "omp workshare" parent
			ASTNode parent = node.parent();
			int parentIndex = getChildIndex(parent, node);
			assert parentIndex != -1;
			parent.setChild(parentIndex, stmt);

			removeOmpConstruct(stmt);

		} else if (node instanceof FunctionCallNode
				&& ((FunctionCallNode) node).getFunction() instanceof IdentifierExpressionNode
				&& ((IdentifierExpressionNode) ((FunctionCallNode) node)
						.getFunction()).getIdentifier().name()
						.startsWith("omp_")) {
			/*
			 * Replace
			 */
			String ompFunctionName = ((IdentifierExpressionNode) ((FunctionCallNode) node)
					.getFunction()).getIdentifier().name();
			ASTNode replacement = null;
			if (ompFunctionName.equals("omp_get_thread_num")) {
				try {
					replacement = nodeFactory.newIntegerConstantNode(
							node.getSource(), "0");
				} catch (SyntaxException e) {
					e.printStackTrace();
				}
			} else if (ompFunctionName.equals("omp_get_num_threads")
					|| ompFunctionName.equals("omp_get_max_threads")
					|| ompFunctionName.equals("omp_get_num_procs")
					|| ompFunctionName.equals("omp_get_thread_limit")) {
				try {
					replacement = nodeFactory.newIntegerConstantNode(
							node.getSource(), "1");
				} catch (SyntaxException e) {
					e.printStackTrace();
				}

			} else if (ompFunctionName.equals("omp_init_lock")
					|| ompFunctionName.equals("omp_set_lock")
					|| ompFunctionName.equals("omp_unset_lock")
					|| ompFunctionName.equals("omp_set_num_threads")) {
				// delete this node
				replacement = nodeFactory
						.newNullStatementNode(node.getSource());

			} else if (ompFunctionName.equals("omp_get_wtime")) {
				// this will be transformed by the OMP transformer

			} else {
				assert false : "Unsupported omp function call "
						+ ompFunctionName
						+ " cannot be replaced by OpenMP simplifier";
			}

			// Link "replacement" into the omp call's parent
			ASTNode parent = node.parent();
			int parentIndex = getChildIndex(parent, node);
			assert parentIndex != -1;
			parent.setChild(parentIndex, replacement);

		} else if (node != null) {
			Iterable<ASTNode> children = node.children();
			for (ASTNode child : children) {
				removeOmpConstruct(child);
			}
		}
	}

	/*
	 * Scan workshares to drive dependence analysis.
	 */
	private void transformOmpWorkshare(ASTNode node) {
		if (node instanceof OmpForNode) {
			OmpForNode ompFor = (OmpForNode) node;
			/*
			 * Determine the private variables since they cannot generate
			 * dependences.
			 * 
			 * TBD: Factor this out to a method and pass it as a parameter to
			 * processFor
			 */
			loopPrivateIDs = new ArrayList<Entity>();
			addEntities(loopPrivateIDs, ompFor.privateList());
			addEntities(loopPrivateIDs, ompFor.copyinList());
			addEntities(loopPrivateIDs, ompFor.copyprivateList());
			addEntities(loopPrivateIDs, ompFor.firstprivateList());
			addEntities(loopPrivateIDs, ompFor.lastprivateList());
			SequenceNode<OmpReductionNode> reductionList = ompFor
					.reductionList();
			if (reductionList != null) {
				for (OmpReductionNode r : reductionList) {
					addEntities(loopPrivateIDs, r.variables());
				}
			}

			processFor(ompFor);
			
			// reset variable to avoid interference with processing of non-loop parallel regions
			loopPrivateIDs = new ArrayList<Entity>();


		} else if (node instanceof OmpSyncNode) {
			OmpSyncNode syncNode = (OmpSyncNode) node;

			OmpSyncNodeKind kind = syncNode.ompSyncNodeKind();
			switch (kind) {
			case MASTER:
				allIndependent = false;
				break;
			case CRITICAL:
				allIndependent = false;
				break;
			case BARRIER:
				allIndependent = false;
				;
				break;
			case ORDERED:
				/*
				 * Should be able to optimize this case since semantics
				 * guarantee serial order
				 */
				allIndependent = false;
				;
				break;
			case FLUSH:
				allIndependent = false;
				;
				break;
			default:
				allIndependent = false;
				break;
			}

		} else if (node instanceof OmpWorksharingNode) {
			OmpWorksharingNode wsNode = (OmpWorksharingNode) node;

			OmpWorksharingNodeKind kind = wsNode.ompWorkshareNodeKind();
			switch (kind) {
			case SECTIONS:
				allIndependent = false;
				break;
			case SECTION:
				allIndependent = false;
				break;
			case SINGLE:
				allIndependent = false;
				break;
			default:
				allIndependent = false;
				break;
			}
			
		} else if (isAssignment(node)) {
			/* Collect up the set of assignment statements that are not within workshares */
			
			/* This code is clunky because it uses globals, but we can accumulate the
			 * read/write sets for these statements within the parallel and then post
			 * process them. 
			 */
						
			// Reset visitor globals
			writeVars = new HashSet<Entity>();
			readVars = new HashSet<Entity>();
			writeArrayRefs = new HashSet<OperatorNode>();
			readArrayRefs = new HashSet<OperatorNode>();
			
			loopPrivateIDs = new ArrayList<Entity>();
			
			collectAssignRefExprs(node);
			
			if (debug) {
				System.out.println("Analyzed non-workshare assignment "+node+" with:");
				System.out.println("   sharedReads = "+readVars);
				System.out.println("   sharedWrites = "+writeVars);
				System.out.println("   sharedArrayReads = "+readArrayRefs);
				System.out.println("   sharedArrayWrites = "+writeArrayRefs);
			}
			
			sharedReads.addAll(readVars);
			sharedWrites.addAll(writeVars);
			sharedArrayReads.addAll(readArrayRefs);
			sharedArrayWrites.addAll(writeArrayRefs);
			
			/*
			 *  TBD: we are not collecting the reads from all of the appropriate statements. 
			 *  For example the reads in the conditions of if/while/for/... 
			 */

		} else if (node != null) {

			// BUG: can get here with null values in parallelfor.c example

			/*
			 * Could match other types here that have no ForLoopNode below them
			 * and skip their traversal to speed things up.
			 */
			Iterable<ASTNode> children = node.children();
			for (ASTNode child : children) {
				transformOmpWorkshare(child);
			}
		}
	}

	/*
	 */
	private void processFor(OmpForNode ompFor) {
		ForLoopNode fln = (ForLoopNode) ompFor.statementNode();

		/*
		 * If the "omp for" has a "nowait" clause then it can still be
		 * transformed as long as its parent is the "omp parallel", i.e., no
		 * additional statements follow it in the "omp parallel"
		 */
		if (ompFor.nowait()) {
			if (!(ompFor.parent() instanceof OmpParallelNode))
				return;
		}

		/*
		 * Need to handle collapse through the use of a sequence of iteration
		 * variables and associated constraints on them.
		 */

		/*
		 * The following block computes the loop appropriate constraints that
		 * bound the loop variable's range.
		 * 
		 * This code handles non-normalized loops, e.g., starting at non-zero
		 * indices, iterating down or up, etc.
		 * 
		 * TBD: record the increment to be used for more precise dependence
		 * constraints.
		 * 
		 * It does not check whether those bounding expressions are loop
		 * invariant, which is required by the OpenMP standard, but it does
		 * enforce a number of other canonical loop form constraints.
		 */
		IdentifierNode loopVariable = null;
		ExpressionNode initBound = null;

		List<ExpressionNode> boundingConditions = new LinkedList<ExpressionNode>();

		{
			ForLoopInitializerNode initializer = fln.getInitializer();
			if (initializer instanceof OperatorNode) {
				OperatorNode assign = (OperatorNode) initializer;
				Operator op = assign.getOperator();
				if (op == Operator.ASSIGN) {
					ExpressionNode left = assign.getArgument(0);
					assert left instanceof IdentifierExpressionNode : "OpenMP Canonical Loop Form violated (identifier required on LHS of initializer)";
					loopVariable = ((IdentifierExpressionNode) left)
							.getIdentifier().copy();
					initBound = assign.getArgument(1).copy();
				} else {
					assert false : "OpenMP Canonical Loop Form violated (initializer must be an assignment) :"
							+ assign;
				}

			} else if (initializer instanceof DeclarationListNode) {
				if (initializer instanceof SequenceNode<?>) {
					@SuppressWarnings("unchecked")
					SequenceNode<VariableDeclarationNode> decls = (SequenceNode<VariableDeclarationNode>) initializer;
					Iterator<VariableDeclarationNode> it = (Iterator<VariableDeclarationNode>) decls
							.iterator();
					VariableDeclarationNode vdn = it.next();
					if (it.hasNext()) {
						assert false : "OpenMP Canonical Loop Form violated (single initializer only) :"
								+ initializer;
					}

					loopVariable = vdn.getEntity().getDefinition()
							.getIdentifier().copy();

					assert vdn.getInitializer() instanceof ExpressionNode : "OpenMP Canonical Loop Form violated (initializer must be simple expression)";

					// Record the initializer expression to build up the
					// initCondition below
					initBound = (ExpressionNode) vdn.getInitializer().copy();
				} else {
					assert false : "Expected SequenceNode<VariableDeclarationNode>: "
							+ initializer;
				}

			} else {
				assert false : "Expected OperatorNode or DeclarationListNode: "
						+ initializer;
			}

			ExpressionNode condition = fln.getCondition();

			if (condition instanceof OperatorNode) {
				OperatorNode relop = (OperatorNode) condition;

				/*
				 * The initial bound of the iteration space is established by an
				 * assignment statement. We need to convert that assignment into
				 * an appropriate inequality to appropriately constrain the loop
				 * variable values. The code assumes that the polarity of the
				 * loop exit condition and the increment operator are
				 * compatible, i.e., a "<" or "<=" test is coupled with an "++"
				 * and a ">" or ">=" with a "--"; this condition is not checked
				 * here. We reverse the polarity of the loop exit condition to
				 * establish the boundary condition associated with the
				 * initialization and make that condition non-strict to account
				 * for the equality implicit in the assignment.
				 * 
				 * This results in the following types of behavior: for (int
				 * i=0; i<N; i++) generates "i>=0" as an "initial" bound for
				 * (int i=0; i<=N-1; i++) generates "i>=0" as an "initial" bound
				 * for (int i=N-1; i>=0; i++) generates "i<=N-1" as an "initial"
				 * bound for (int i=N-1; i>-1; i++) generates "i<=N-1" as an
				 * "initial" bound
				 */
				List<ExpressionNode> arguments = new LinkedList<ExpressionNode>();
				ExpressionNode lvNode = nodeFactory
						.newIdentifierExpressionNode(ompFor.getSource(),
								loopVariable);
				arguments.add(lvNode);
				arguments.add(initBound);

				Operator op = relop.getOperator();
				if (op == Operator.LT || op == Operator.LTE) {
					OperatorNode newBoundExpr = nodeFactory.newOperatorNode(
							ompFor.getSource(), Operator.GTE, arguments);
					boundingConditions.add(newBoundExpr);

				} else if (op == Operator.GT || op == Operator.GTE) {
					OperatorNode newBoundExpr = nodeFactory.newOperatorNode(
							ompFor.getSource(), Operator.LTE, arguments);
					boundingConditions.add(newBoundExpr);
				} else {
					assert false : "OpenMP Canonical Loop Form violated (condition must be one of >, >=, <, or <=) :"
							+ relop;
				}

				ExpressionNode left = relop.getArgument(0);
				ExpressionNode right = relop.getArgument(1);

				/*
				 * variable must be either left or right, but not both
				 * 
				 * Currently these checks are based on the name of the variable.
				 * Perhaps it is better to use the symbol information, i.e.,
				 * getEntity()
				 */
				int loopVariableCount = 0;
				if (left instanceof IdentifierExpressionNode) {
					IdentifierNode id = ((IdentifierExpressionNode) left)
							.getIdentifier();
					if (id.name().equals(loopVariable.name())) {
						loopVariableCount++;
					}
				}

				if (right instanceof IdentifierExpressionNode) {
					IdentifierNode id = ((IdentifierExpressionNode) right)
							.getIdentifier();
					if (id.name().equals(loopVariable.name())) {
						loopVariableCount++;
					}
				}

				if (loopVariableCount == 1) {
					boundingConditions.add(condition);
				} else {
					assert false : "OpenMP Canonical Loop Form violated (requires variable condition operand) :"
							+ condition;
				}
			} else {
				assert false : "OpenMP Canonical Loop Form violated (condition malformed) :"
						+ condition;
			}

		}

		/*
		 * Accumulate the set of memory-referencing expressions, i.e., variable
		 * references, array index expressions, on the LHS and the RHS.
		 * 
		 * TBD: Need to generalize this to record the full alias-equivalence
		 * relation. - parameters of the same type are potential aliases unless
		 * the "restrict" keyword is used - assignments through pointers need to
		 * be handled as well
		 * 
		 * TBD: We need to know the dimensions of array parameters or else we
		 * cannot reason about independent memory regions, e.g., indexing of the
		 * end of one array may touch an element of an adjacent array.
		 */
		StatementNode body = fln.getBody();
		writeVars = new HashSet<Entity>();
		readVars = new HashSet<Entity>();
		writeArrayRefs = new HashSet<OperatorNode>();
		readArrayRefs = new HashSet<OperatorNode>();

		collectAssignRefExprs(body);

		/*
		 * Check for name-based dependences
		 */
		writeVars.retainAll(readVars);
		boolean independent = writeVars.isEmpty();

		/*
		 * Check for array-based dependences.
		 */

		independent &= noArrayRefDependences(boundingConditions,
				writeArrayRefs, readArrayRefs);

		if (debug) {
			System.out.println("Found "+(independent?"independent":"dependent")+" OpenMP for "+ompFor);
			System.out.println("  writeVars : "+writeVars);
			System.out.println("  readVars : "+readVars);
			System.out.println("  writeArrays : "+writeArrayRefs);
			System.out.println("  readArrays : "+readArrayRefs);
		}

		if (independent) {
			/*
			 * At this point we can create a branch in the program based on the
			 * boundingConditions and array's reference expressions. Essentially
			 * we want to construct a runtime predicate that captures the
			 * assumptions about referenced memory locations that led to the
			 * judgement of independence.
			 * 
			 * For example if the program had for (int i=0; i<N; i++) a[i] =
			 * b[i]; then we want to generate a condition that says that: a != b
			 * && a+(N-1) < b && b+(N-1) < a which ensures that the array
			 * regions that are accessed are disjoint.
			 * 
			 * Note that this would approach could generalize to more
			 * interesting cases: for (int i=0; i<(N/2); i++) a[i] = a[N-1-i];
			 */

			/*
			 * Transform this "omp for" into a "omp single" workshare. To safely
			 * perform this when a reduction is present for an (op,var) pair all
			 * assignments to "var" in the "omp for" must be of the form
			 * "var = var op ...".
			 */
			SequenceNode<OmpReductionNode> reductionList = ompFor
					.reductionList();
			List<IdentifierNode> reductionVariables = null;
			boolean safeReduction = true;

			if (reductionList != null) {
				reductionVariables = new ArrayList<IdentifierNode>();

				// Build a map for scanning for reduction variable operator
				// assignment consistency
				Map<Entity, Operator> idOpMap = new HashMap<Entity, Operator>();
				for (OmpReductionNode r : reductionList) {
					if (r instanceof OmpSymbolReductionNode) {
						Operator op = ((OmpSymbolReductionNode) r).operator();
						for (IdentifierExpressionNode id : r.variables()) {
							idOpMap.put(id.getIdentifier().getEntity(), op);
							reductionVariables.add(id.getIdentifier());
						}
						safeReduction &= checkReductionAssignments(fln, idOpMap);
					} else {
						safeReduction = false;
						break;
					}
				}
			}

			if (safeReduction) {
				ASTNode parent = ompFor.parent();
				int ompForIndex = getChildIndex(parent, ompFor);
				assert ompForIndex != -1;
				parent.removeChild(ompForIndex);

				fln.parent().removeChild(fln.childIndex());
				OmpWorksharingNode single = nodeFactory.newOmpSingleNode(
						ompFor.getSource(), fln);

				// Transfer private, firstprivate, copyprivate, and nowait
				// clauses to single

				SequenceNode<IdentifierExpressionNode> singlePrivateList = ompFor
						.privateList();
				SequenceNode<IdentifierExpressionNode> singleFirstPrivateList = ompFor
						.firstprivateList();
				SequenceNode<IdentifierExpressionNode> singleCopyPrivateList = ompFor
						.copyprivateList();

				// Add iteration variable to private list for single
				IdentifierExpressionNode privateLoopVariable = nodeFactory
						.newIdentifierExpressionNode(
								single.getSource(),
								nodeFactory.newIdentifierNode(
										single.getSource(), loopVariable.name()));
				if (ompFor.privateList() == null) {
					List<IdentifierExpressionNode> l = new ArrayList<IdentifierExpressionNode>();
					l.add(privateLoopVariable);
					singlePrivateList = nodeFactory.newSequenceNode(
							ompFor.getSource(), "private", l);
				} else {
					singlePrivateList.addSequenceChild(privateLoopVariable);
				}

				single.setPrivateList(singlePrivateList);
				single.setFirstprivateList(singleFirstPrivateList);

				// Any reduction variables should be added to copyprivate
				if (reductionVariables != null) {
					List<IdentifierExpressionNode> l = new ArrayList<IdentifierExpressionNode>();
					for (IdentifierNode id : reductionVariables) {
						l.add(nodeFactory.newIdentifierExpressionNode(
								single.getSource(),
								nodeFactory.newIdentifierNode(
										single.getSource(), id.name())));
					}
					if (ompFor.copyprivateList() == null) {
						singleCopyPrivateList = nodeFactory.newSequenceNode(
								ompFor.getSource(), "copyprivate", l);
					} else {
						for (IdentifierExpressionNode ide : l) {
							singleCopyPrivateList.addSequenceChild(ide);
						}
					}
				}

				single.setCopyprivateList(singleCopyPrivateList);
				single.setNowait(ompFor.nowait());

				parent.setChild(ompForIndex, single);
			}
		}

		allIndependent &= independent;

	}

	private boolean checkReductionAssignments(ASTNode node,
			Map<Entity, Operator> idOpMap) {
		return checkReductionWorker(node, idOpMap, true);
	}

	private boolean checkReductionWorker(ASTNode node,
			Map<Entity, Operator> idOpMap, boolean consistent) {
		if (node instanceof OperatorNode) {
			/*
			 * Access the LHS to prepare for operator comparison
			 */
			ExpressionNode lhs = ((OperatorNode) node).getArgument(0);
			if (lhs instanceof IdentifierExpressionNode) {
				Entity idEnt = ((IdentifierExpressionNode) lhs).getIdentifier()
						.getEntity();
				if (idOpMap.keySet().contains(idEnt)) {
					Operator op = idOpMap.get(idEnt);

					switch (((OperatorNode) node).getOperator()) {
					case ASSIGN:
						ExpressionNode rhs = ((OperatorNode) node)
								.getArgument(1);
						if (rhs instanceof OperatorNode) {
							consistent &= (eqOpToOp(op) == ((OperatorNode) rhs)
									.getOperator());
						} else {
							consistent = false;
						}
						break;
					case BITANDEQ:
					case BITOREQ:
					case BITXOREQ:
					case MINUSEQ:
					case PLUSEQ:
					case TIMESEQ:
						consistent &= (((OperatorNode) node).getOperator() == op);
						break;
					default:
					}
				}
			}

		} else if (node != null) {
			Iterable<ASTNode> children = node.children();
			for (ASTNode child : children) {
				consistent &= checkReductionWorker(child, idOpMap, consistent);
			}
		}
		return consistent;
	}

	/*
	 * Returns the index of "child" in the children of "node"; -1 if "child" is
	 * not one of "node"'s children.
	 */
	private int getChildIndex(ASTNode node, ASTNode child) {
		for (int childIndex = 0; childIndex < node.numChildren(); childIndex++) {
			if (node.child(childIndex) == child)
				return childIndex;
		}
		return -1;
	}

	private Operator eqOpToOp(Operator op) {
		switch (op) {
		case BITANDEQ:
			return Operator.BITAND;
		case BITOREQ:
			return Operator.BITOR;
		case BITXOREQ:
			return Operator.BITXOR;
		case MINUSEQ:
			return Operator.MINUS;
		case PLUSEQ:
			return Operator.PLUS;
		case TIMESEQ:
			return Operator.TIMES;
		default:
		}
		return op;
	}
	
	private boolean isAssignment(ASTNode node) {
		return (node instanceof OperatorNode) &&
				(  ((OperatorNode) node).getOperator() == Operator.ASSIGN
				|| ((OperatorNode) node).getOperator() == Operator.PLUSEQ
				|| ((OperatorNode) node).getOperator() == Operator.POSTINCREMENT
				|| ((OperatorNode) node).getOperator() == Operator.POSTDECREMENT);
	}

	/*
	 * This is a visitor that processes assignment statements.
	 * 
	 * It detects when it descends into a critical section and ignores writes to
	 * shared variables nested within.
	 */
	private void collectAssignRefExprs(ASTNode node) {
		if (node instanceof OmpSyncNode
				&& ((OmpSyncNode) node).ompSyncNodeKind() == OmpSyncNode.OmpSyncNodeKind.CRITICAL) {
			// Do not collect read/write references from critical sections
			return;
		} else if (isAssignment(node)) {
			/*
			 * Need to handle all of the *EQ operators as well.
			 */
			OperatorNode assign = (OperatorNode) node;

			ExpressionNode lhs = assign.getArgument(0);
			if (lhs instanceof IdentifierExpressionNode) {
				Entity idEnt = ((IdentifierExpressionNode) lhs)
						.getIdentifier().getEntity();
				if (!privateIDs.contains(idEnt)
						&& !loopPrivateIDs.contains(idEnt)) {
					writeVars.add(idEnt);
				}
			} else if (lhs instanceof OperatorNode
					&& ((OperatorNode) lhs).getOperator() == Operator.SUBSCRIPT) {
				Entity idEnt = baseArray((OperatorNode) lhs)
						.getIdentifier().getEntity();
				if (!privateIDs.contains(idEnt)
						&& !loopPrivateIDs.contains(idEnt)) {
					writeArrayRefs.add((OperatorNode) lhs);
				}

			} else {
				
			}

			// The argument at index 1 is the RHS.   If there is no RHS then this is a unary assignment and
			// we should collect from argument 0.
			ASTNode rhs = (assign.getNumberOfArguments() > 1) ? assign.getArgument(1) : lhs;

			collectRHSRefExprs(rhs);
			
		} else if (node instanceof IfNode) {
			// Collect up the expressions from other statements
			IfNode ifn = (IfNode)node;
			collectRHSRefExprs(ifn.getCondition());
			collectAssignRefExprs(ifn.getTrueBranch());
			if (ifn.getTrueBranch() != null) {
				collectAssignRefExprs(ifn.getFalseBranch());
			}
			
		} else if (node instanceof LoopNode) {
			LoopNode loopn = (LoopNode)node;
			collectRHSRefExprs(loopn.getCondition());
			collectAssignRefExprs(loopn.getBody());
			
			if (loopn instanceof ForLoopNode) {
				ForLoopNode forn = (ForLoopNode)loopn;
				collectAssignRefExprs(forn.getInitializer());
				collectAssignRefExprs(forn.getIncrementer());
			}
			
		} else if (node instanceof SwitchNode) {
			SwitchNode switchn = (SwitchNode)node;
			collectRHSRefExprs(switchn.getCondition());
			collectAssignRefExprs(switchn.getBody());

		} else if (node instanceof ReturnNode) {
			ReturnNode returnn = (ReturnNode)node;
			if (returnn.getExpression() != null) {
				collectAssignRefExprs(returnn.getExpression());
			}

		} else if (node != null) {
			// BUG: can get here with null values in parallelfor.c example

			/*
			 * Could match other types here that have no ForLoopNode below them
			 * and skip their traversal to speed things up.
			 */
			Iterable<ASTNode> children = node.children();
			for (ASTNode child : children) {
				collectAssignRefExprs(child);
			}
		}
	}

	/*
	 * This is a visitor that processes assignment statements
	 */
	private void collectRHSRefExprs(ASTNode node) {
		if (node instanceof IdentifierExpressionNode) {
			Entity idEnt = ((IdentifierExpressionNode) node).getIdentifier()
					.getEntity();
			if (!privateIDs.contains(idEnt) && !loopPrivateIDs.contains(idEnt)) {
				readVars.add(idEnt);
			}

		} else if (node instanceof OperatorNode
				&& ((OperatorNode) node).getOperator() == Operator.SUBSCRIPT) {
			Entity idEnt = baseArray((OperatorNode) node).getIdentifier()
					.getEntity();
			if (!privateIDs.contains(idEnt) && !loopPrivateIDs.contains(idEnt)) {
				readArrayRefs.add((OperatorNode) node);
			}

		} else if (node != null) {
			// BUG: can get here with null values in parallelfor.c example

			/*
			 * Could match other types here that have no ForLoopNode below them
			 * and skip their traversal to speed things up.
			 */
			Iterable<ASTNode> children = node.children();
			for (ASTNode child : children) {
				collectRHSRefExprs(child);
			}
		}
	}

	/*
	 * Check array read/write sets for dependences
	 * 
	 * This code formulates a logical constraint for each pair of array refs on
	 * the LHS and RHS of the loop.
	 * 
	 * If there exists in the loop, statements of the form: a[e1] = ... and ...
	 * = ... a[e2] ... where e1 and e2 are expressions written in terms of the
	 * loop index variable, then it must be the case that for all values of the
	 * index variable that satisfy initCondition and exitCondition that e1 ==
	 * e2.
	 * 
	 * TBD: Currently this analysis does not handle copy statements and may
	 * therefore overestimate dependences
	 * 
	 * TBD: Currently this code assumes that one dimension is dependent on the
	 * for iteration variables. Needs to be extended for collapse.
	 */
	private boolean noArrayRefDependences(
			List<ExpressionNode> boundingConditions, Set<OperatorNode> writes,
			Set<OperatorNode> reads) {
		for (OperatorNode w : writes) {
			IdentifierExpressionNode baseWrite = baseArray(w);

			for (OperatorNode r : reads) {
				IdentifierExpressionNode baseRead = baseArray(r);

				if (baseWrite.getIdentifier().getEntity() == baseRead
						.getIdentifier().getEntity()) {
					// Need to check logical equality of these expressions
					if (!ExpressionEvaluator.checkEqualityWithConditions(
							indexExpression(w, 1), indexExpression(r, 1),
							boundingConditions)) {
						return false;
					}
				}
			}
		}
		return true;
	}
	
	/* This is a weaker version of the test that just compares base arrays */
	private boolean noArrayRefDependences(Set<OperatorNode> writes, Set<OperatorNode> reads) {
		for (OperatorNode w : writes) {
			IdentifierExpressionNode baseWrite = baseArray(w);

			for (OperatorNode r : reads) {
				IdentifierExpressionNode baseRead = baseArray(r);

				if (baseWrite.getIdentifier().getEntity() == baseRead
						.getIdentifier().getEntity()) {
						return false;
				}
			}
		}
		return true;
	}

	/*
	 * Determine whether node lexically contains an omp construct
	 */
	private boolean hasOmpConstruct(ASTNode node) {
		boolean result = false;
		if (node instanceof OmpNode) {
			result = true;
		} else if (node instanceof FunctionCallNode
				&& ((FunctionCallNode) node).getFunction() instanceof IdentifierExpressionNode
				&& ((IdentifierExpressionNode) ((FunctionCallNode) node)
						.getFunction()).getIdentifier().name()
						.startsWith("omp_")) {
			result = true;
		} else if (node != null) {
			Iterable<ASTNode> children = node.children();
			for (ASTNode child : children) {
				result |= hasOmpConstruct(child);
				if (result)
					break;
			}
		}
		return result;
	}

	/*
	 * For a given subscript node recursively traverse down the 0th argument of
	 * the nested subscript expressions to return the base array identifier.
	 */
	private IdentifierExpressionNode baseArray(OperatorNode subscript) {
		assert subscript.getOperator() == OperatorNode.Operator.SUBSCRIPT : "Expected subscript expression";
		if (subscript.getArgument(0) instanceof IdentifierExpressionNode) {
			return (IdentifierExpressionNode) subscript.getArgument(0);
		}
		return baseArray((OperatorNode) subscript.getArgument(0));
	}

	/*
	 * For multi-dimensional arrays the index expressions are nested in reverse
	 * order of source text nesting. The 1st index is the deepest, etc. Here we
	 * recurse down the 0th argument then count back up to return the
	 * appropriate index expression.
	 */
	private ExpressionNode indexExpression(OperatorNode subscript, int dimension) {
		assert subscript.getOperator() == OperatorNode.Operator.SUBSCRIPT : "Expected subscript expression";
		int d = indexExpressionDepth(subscript) - dimension;
		return indexExpressionAtDepth(subscript, d);
	}

	private ExpressionNode indexExpressionAtDepth(OperatorNode subscript,
			int depth) {
		assert subscript.getOperator() == OperatorNode.Operator.SUBSCRIPT : "Expected subscript expression";
		if (depth == 0) {
			return (ExpressionNode) subscript.getArgument(1);
		}
		return indexExpressionAtDepth(subscript, depth - 1);
	}

	private int indexExpressionDepth(OperatorNode subscript) {
		assert subscript.getOperator() == OperatorNode.Operator.SUBSCRIPT : "Expected subscript expression";
		if (subscript.getArgument(0) instanceof IdentifierExpressionNode) {
			return 1;
		}
		return indexExpressionDepth((OperatorNode) subscript.getArgument(0)) + 1;
	}

}
