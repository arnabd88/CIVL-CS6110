package edu.udel.cis.vsl.civl.transform.common;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.entity.IF.Entity;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.AttributeKey;
import edu.udel.cis.vsl.abc.ast.node.IF.ExternalDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpForNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpParallelNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpReductionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpWorksharingNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpWorksharingNode.OmpWorksharingNodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.DeclarationListNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ForLoopInitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ForLoopNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
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

	private AttributeKey dependenceKey;

	// Visitor identifies scalars through their "defining" declaration
	private Set<Entity> writeVars;
	private Set<Entity> readVars;

	private Set<OperatorNode> writeArrayRefs;
	private Set<OperatorNode> readArrayRefs;

	private boolean allIndependent;

	private List<Entity> privateIDs;
	private List<Entity> loopPrivateIDs;

	public OpenMPSimplifierWorker(ASTFactory astFactory) {
		super("OpenMPSimplifier", astFactory);
	}

	@Override
	public AST transform(AST unit) throws SyntaxException {
		SequenceNode<ExternalDefinitionNode> rootNode = unit.getRootNode();

		assert this.astFactory == unit.getASTFactory();
		assert this.nodeFactory == astFactory.getNodeFactory();
		unit.release();

		// System.out.println("OpenMP Simplifier Activated");
		transformOmpParallel(rootNode);

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
	 * Generically traverse the AST. When an OmpParallel node is encountered
	 * traverse it to detect workshares, analyze their independence, and
	 * transform those workshares.
	 */
	private void transformOmpParallel(ASTNode node) {
		if (node instanceof OmpParallelNode) {
			// System.out.println("OpenMP Simplifier : Found Parallel "+node);

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

			addEntities(privateIDs, ((OmpParallelNode) node).privateList());
			addEntities(privateIDs, ((OmpParallelNode) node).copyinList());
			addEntities(privateIDs, ((OmpParallelNode) node).copyprivateList());
			addEntities(privateIDs, ((OmpParallelNode) node).firstprivateList());
			addEntities(privateIDs, ((OmpParallelNode) node).lastprivateList());
			SequenceNode<OmpReductionNode> reductionList = ((OmpParallelNode) node)
					.reductionList();
			if (reductionList != null) {
				for (OmpReductionNode r : reductionList) {
					addEntities(privateIDs, r.variables());
				}
			}

			allIndependent = true;

			// Visit the rest of this node
			Iterable<ASTNode> children = node.children();
			for (ASTNode child : children) {
				transformOmpWorkshare(child);
			}

			if (allIndependent) {
				/*
				 * Remove the nested omp constructs, e.g., workshares, calls to
				 * omp_*
				 */
				children = node.children();
				for (ASTNode child : children) {
					removeOmpConstruct(child);
				}

				// Remove "statement" node from "omp parallel" node
				StatementNode stmt = ((OmpStatementNode) node).statementNode();
				int stmtIndex = getChildIndex(node, stmt);
				assert stmtIndex != -1;
				node.removeChild(stmtIndex);

				// Link "statement" into the "omp parallel" parent
				ASTNode parent = node.parent();
				int parentIndex = getChildIndex(parent, node);
				assert parentIndex != -1;
				parent.setChild(parentIndex, stmt);
			}

		} else if (node != null) {
			// BUG: can get here with null values in parallelfor.c example

			/*
			 * Could match other types here that have no ForLoopNode below them
			 * and skip their traversal to speed things up.
			 */
			Iterable<ASTNode> children = node.children();
			for (ASTNode child : children) {
				transformOmpParallel(child);
			}
		}
	}

	/*
	 * This method assumes that all of the OMP workshares that are encountered
	 * can be safely removed or transformed into non-OMP equivalents.
	 */
	private void removeOmpConstruct(ASTNode node) {
		if (node instanceof OmpWorksharingNode) {
			// Remove "statement" node from "omp workshare" node
			StatementNode stmt = ((OmpStatementNode) node).statementNode();
			int stmtIndex = getChildIndex(node, stmt);
			assert stmtIndex != -1;
			node.removeChild(stmtIndex);

			// Link "statement" into the "omp workshare" parent
			ASTNode parent = node.parent();
			int parentIndex = getChildIndex(parent, node);
			assert parentIndex != -1;
			parent.setChild(parentIndex, stmt);

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
			} else if (ompFunctionName.equals("omp_get_num_threads") ||
			           ompFunctionName.equals("omp_get_max_threads") ||
			           ompFunctionName.equals("omp_get_num_procs") ||
			           ompFunctionName.equals("omp_get_thread_limit")) {
				try {
					replacement = nodeFactory.newIntegerConstantNode(
							node.getSource(), "1");
				} catch (SyntaxException e) {
					e.printStackTrace();
				}
				
			} else if (ompFunctionName.equals("omp_init_lock") || 
					ompFunctionName.equals("omp_set_lock") || 
					ompFunctionName.equals("omp_unset_lock") || 
					ompFunctionName.equals("omp_set_num_threads")) {
				// delete this node
				replacement = nodeFactory.newNullStatementNode(node.getSource());
				
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

	private void transformOmpWorkshare(ASTNode node) {
		if (node instanceof OmpForNode) {
			OmpForNode ompFor = (OmpForNode) node;
			// System.out.println("OpenMP Simplifier : Found For "+node);

			/*
			 * Determine the private variables since they cannot generate
			 * dependences.
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

			// Record of independent workshare is computed in processFor

		} else if (node instanceof OmpWorksharingNode) {
			OmpWorksharingNode wsNode = (OmpWorksharingNode) node;
			// System.out.println("OpenMP Simplifier : Found Workshare "+node);

			OmpWorksharingNodeKind kind = wsNode.ompWorkshareNodeKind();
			switch (kind) {
			case SECTIONS:
				processSections(wsNode);
				allIndependent = false;
				break;
			case SECTION:
				allIndependent = false;
				break;
			case SINGLE:
				allIndependent &= true;
				break;
			default:
				allIndependent = false;
				break;
			}

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

	// need to refactor the analysis code to apply to individual section/for
	// body

	// need to collect up a sequence of sections/for bodies to be subjected to
	// analysis. this should be done in the high-level pass above.

	private void processSections(OmpWorksharingNode ompSections) {
	}

	/*
	 */
	private void processFor(OmpForNode ompFor) {
		ForLoopNode fln = (ForLoopNode) ompFor.statementNode();

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
		 * This is a flow-insensitive analysis which makes the treatment of
		 * NOWAIT possible, but means that precision may be sacrificed.
		 * 
		 * TBD: extend this to handle NOWAIT clauses on loops. This must be done
		 * "higher up" in the AST until the next barrier is reached (either
		 * explicit or implicit).
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
		boolean hasDeps = !writeVars.isEmpty();

		/*
		 * Check for array-based dependences.
		 */
		hasDeps |= hasArrayRefDependences(boundingConditions, writeArrayRefs,
				readArrayRefs);
		/*
		 * System.out.println("Found "+(hasDeps?"dependent":"independent")+" loop "
		 * +ompFor+"\nwith the following:");
		 * System.out.println("  writeVars : "+writeVars);
		 * System.out.println("  readVars : "+readVars);
		 * System.out.println("  writeArrays : "+writeArrayRefs);
		 * System.out.println("  readArrays : "+readArrayRefs);
		 */

		if (!hasDeps) {
			/*
			 * Transform this OpenMP "for" into a "single" workshare
			 */
			ASTNode parent = ompFor.parent();
			{
				int ompForIndex = getChildIndex(parent, ompFor);
				assert ompForIndex != -1;
				parent.removeChild(ompForIndex);

				fln.parent().removeChild(fln.childIndex());
				OmpWorksharingNode single = nodeFactory.newOmpSingleNode(
						ompFor.getSource(), fln);

				// Transfer private, firstprivate, copyprivate, and nowait
				// clauses to single
				single.setPrivateList(ompFor.privateList());
				single.setFirstprivateList(ompFor.firstprivateList());
				single.setCopyprivateList(ompFor.copyprivateList());
				single.setNowait(ompFor.nowait());

				parent.setChild(ompForIndex, single);
			}
		}

		allIndependent &= !hasDeps;

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

	/*
	 * This is a visitor that processes assignment statements
	 */
	private void collectAssignRefExprs(ASTNode node) {
		if (node instanceof OperatorNode
				&& ((OperatorNode) node).getOperator() == Operator.ASSIGN) {
			/*
			 * Need to handle all of the *EQ operators as well.
			 */
			OperatorNode assign = (OperatorNode) node;

			ExpressionNode lhs = assign.getArgument(0);
			if (lhs instanceof IdentifierExpressionNode) {
				Entity idEnt = ((IdentifierExpressionNode) lhs).getIdentifier()
						.getEntity();
				if (!privateIDs.contains(idEnt)
						&& !loopPrivateIDs.contains(idEnt)) {
					writeVars.add(idEnt);
				}
			} else if (lhs instanceof OperatorNode
					&& ((OperatorNode) lhs).getOperator() == Operator.SUBSCRIPT) {
				writeArrayRefs.add((OperatorNode) lhs);

			} else {
				// System.out.println("DependenceAnnotator found lhs:" + lhs);
			}

			// The argument at index 1 is the RHS
			collectRHSRefExprs(assign.getArgument(1));

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
			readArrayRefs.add((OperatorNode) node);

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
	 * TBD: Currently this code only handles single dimensional arrays
	 */
	private boolean hasArrayRefDependences(
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
						return true;
					}
				}
			}
		}
		return false;
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
