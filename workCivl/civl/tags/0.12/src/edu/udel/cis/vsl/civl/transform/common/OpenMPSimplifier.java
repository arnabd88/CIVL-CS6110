package edu.udel.cis.vsl.civl.transform.common;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.entity.IF.Entity;
import edu.udel.cis.vsl.abc.ast.entity.IF.Variable;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.AttributeKey;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpForNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpParallelNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpWorksharingNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpWorksharingNode.OmpWorksharingNodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.DeclarationListNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ForLoopInitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ForLoopNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.ast.util.ExpressionEvaluator;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;

/**
 * This transformer analyzes OpenMP constructs and converts them to simpler,
 * i.e., less concurrent, instances of constructs.
 * 
 * This transform operates in two phases:
 * 
 * 1) Analyze OpenMP workshares to determine those that are provably
 * thread-independent, i.e., execution of workshares in parallel is guaranteed
 * to compute the same result. 2) Transform OpenMP constructs based on the
 * analysis results.
 * 
 * @author dwyer
 * 
 */
public class OpenMPSimplifier extends CIVLBaseTransformer {

	public final static String CODE = "omp";
	public final static String LONG_NAME = "OpenMPSimplifier";
	public final static String SHORT_DESCRIPTION = "simplifies independent C/OpenMP constructs";

	private AttributeKey dependenceKey;

	// Visitor identifies scalars through their "defining" declaration
	private Set<Entity> writeVars;
	private Set<Entity> readVars;

	private Set<OperatorNode> writeArrayRefs;
	private Set<OperatorNode> readArrayRefs;

	private List<Entity> privateIDs;

	public OpenMPSimplifier(ASTFactory astFactory, CIVLConfiguration config) {
		super(CODE, LONG_NAME, SHORT_DESCRIPTION, astFactory, config);
	}

	public AST transform(AST unit) throws SyntaxException {
		ASTNode rootNode = unit.getRootNode();

		assert this.astFactory == unit.getASTFactory();
		assert this.nodeFactory == astFactory.getNodeFactory();
		unit.release();

		//System.out.println("LoopDependenceAnnotator Activated");
		transformOmpParallel(rootNode);

		return astFactory.newAST(rootNode);
	}

	AttributeKey getAttributeKey() {
		return this.dependenceKey;
	}

	/*
	 * Generically traverse the AST. When an OmpParallel node is encountered 
	 * traverse it to detect workshares, analyze their independence, and
	 * transform those workshares.
	 */
	private void transformOmpParallel(ASTNode node) {
		if (node instanceof OmpParallelNode) {
			/*
			 * TBD: this code does not yet handle: - nested parallel blocks -
			 * sections workshares - collapse clauses - chunk clauses -
			 * multi-dimensional arrays
			 */

			/*
			 * Determine the private variables since they cannot generate
			 * dependences. Look at default clauses, private clauses,
			 * threadprivate directives (global somewhere?)
			 */
			SequenceNode<IdentifierExpressionNode> privateList = ((OmpParallelNode) node)
					.privateList();
			if (privateList != null) {
				privateIDs = new ArrayList<Entity>();
				for (IdentifierExpressionNode idExpression : privateList) {
					Entity idEnt = idExpression.getIdentifier().getEntity();

					privateIDs.add(idEnt);
				}
			} else {
				privateIDs = null;
			}
			//System.out.println("Found OmpParallelNode with private:"
			//		+ privateIDs);

			// Visit the rest of this node
			Iterable<ASTNode> children = node.children();
			for (ASTNode child : children) {
				transformOmpWorkshare(child);
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
	
	private void transformOmpWorkshare(ASTNode node) {
		if (node instanceof OmpForNode) {
			OmpForNode ompFor = (OmpForNode) node;

			processFor(ompFor);
			
		} else if (node instanceof OmpWorksharingNode) {
			OmpWorksharingNode wsNode = (OmpWorksharingNode)node;
			OmpWorksharingNodeKind kind = wsNode.ompWorkshareNodeKind();
			if (kind == OmpWorksharingNode.OmpWorksharingNodeKind.SECTIONS) {
				processSections(wsNode);
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
	
	// need to refactor the analysis code to apply to individual section/for body
	
	// need to collect up a sequence of sections/for bodies to be subjected to
	// analysis.  this should be done in the high-level pass above.  
	
	private void processSections(OmpWorksharingNode ompSections) {
	}

	private void processFor(OmpForNode ompFor) {
		/*
		 * We do not currently check for issues with canonical form.
		 * Compilers are not required to check those constraints, so thee is
		 * some value in doing so.
		 */
		ForLoopNode fln = (ForLoopNode) ompFor.statementNode();

		/*
		 * Condition must be of the form: var relop expr or expr relop var
		 * collect this expression - call it "endBound" record the direction
		 * of the test (i.e., less/greater)
		 */
		@SuppressWarnings("unused")
		boolean lessThanComparison = true;
		IdentifierNode loopVariable = null;
		ExpressionNode condition = fln.getCondition();

		if (condition instanceof OperatorNode) {
			OperatorNode relop = (OperatorNode) condition;
			Operator op = relop.getOperator();
			if (op == Operator.LT || op == Operator.LTE) {
				lessThanComparison = true;
			} else if (op == Operator.GT || op == Operator.GTE) {
				lessThanComparison = false;
			} else {
				assert false : "OpenMP Canonical Loop Form violated (condition must be one of >, >=, <, or <=) :"
						+ relop;
			}

			ExpressionNode left = relop.getArgument(0);
			ExpressionNode right = relop.getArgument(1);

			// variable may be either left or right.
			if (left instanceof IdentifierExpressionNode) {
				loopVariable = ((IdentifierExpressionNode) left)
						.getIdentifier();
			} else if (right instanceof IdentifierExpressionNode) {
				loopVariable = ((IdentifierExpressionNode) right)
						.getIdentifier();
			} else {
				assert false : "OpenMP Canonical Loop Form violated (requires variable condition operand) :"
						+ condition;
			}
		} else {
			assert false : "OpenMP Canonical Loop Form violated (condition malformed) :"
					+ condition;
		}

		/*
		 * Could check here to ensure that the increment matches the
		 * ordering, i.e., increment positively for "less" and negatively
		 * for "greater", and magnitude constraints of OpenMP. This may
		 * require knowing the sign of the "incr" in the OpenMP canonical
		 * loop form (section 2.6 of the manual), but this would be easy to
		 * assert for checking at runtime.
		 */
		@SuppressWarnings("unused")
		ExpressionNode incrementer = fln.getIncrementer();

		/*
		 * Initializer must be of the form: (type?) var = expr which appears
		 * as either a DeclarationList or OperatorExpression
		 * 
		 * Need to compute collect name of var and expression construct an
		 * expression that honors the ordering of the test e.g., if less
		 * then create "var >= expression" call the resulting expression
		 * "beginBound"
		 */
		ForLoopInitializerNode initializer = fln.getInitializer();
		if (initializer instanceof OperatorNode) {
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

				Variable v = vdn.getEntity();
				if (v != loopVariable.getEntity()) {
					assert false : "OpenMP Canonical Loop Form violated (initializer/condition variable mismatch) :"
							+ initializer;

				}

			} else {
				assert false : "Expected SequenceNode<VariableDeclarationNode>: "
						+ initializer;
			}

		} else {
			assert false : "Expected OperatorNode or DeclarationListNode: "
					+ initializer;
		}

		/*
		 * A challenge that we do not consider here is ensuring that certain
		 * expressions in the increment and test are loop invariant.
		 * 
		 * Note that we set up "beginBound" and "endBound" to be used to
		 * constraint the range of the index expression in case it is needed
		 * in determining the equivalence of loop index expressions. These
		 * bounds are currently not used in formulating the SARL queries.
		 */

		/*
		 * Accumulate the set of memory-referencing expressions, i.e.,
		 * variable references, array index expressions, on the LHS and the
		 * RHS.
		 * 
		 * This is a flow-insensitive analysis which makes the treatment of
		 * NOWAIT possible, but means that precision may be sacrificed.
		 * 
		 * TBD: extend this to handle NOWAIT clauses on loops. This must be
		 * done "higher up" in the AST until the next barrier is reached
		 * (either explicit or implicit).
		 */
		StatementNode body = fln.getBody();
		writeVars = new HashSet<Entity>();
		readVars = new HashSet<Entity>();
		writeArrayRefs = new HashSet<OperatorNode>();
		readArrayRefs = new HashSet<OperatorNode>();

		collectAssignRefExprs(body);

		// System.out.println("Loop Dependence Analysis Info:");
		// System.out.println("   writeVars:" + writeVars);
		// System.out.println("   readVars:" + readVars);
		// System.out.println("   writeArrayRefs:" + writeArrayRefs);
		// System.out.println("   readArrayRefs:" + readArrayRefs);

		/*
		 * Check for name-based dependences
		 */
		writeVars.retainAll(readVars);
		boolean hasDeps = !writeVars.isEmpty();
		// System.out.println("OMP For has scalar "
		// + (writeVars.isEmpty() ? "in" : "")
		// + "dependent loop iterations");

		/*
		 * Check for array-based dependences
		 */
		hasDeps |= hasArrayRefDependences(writeArrayRefs, readArrayRefs);
		// System.out.println("OMP For has array " + (hasDeps ? "" : "in")
		// + "dependent loop iterations");

		if (!hasDeps) {
			/*
			 * Transform this OpenMP "for" into either: 1) a plain loop if
			 * parent is an OpenMP "parallel" statement 2) otherwise a
			 * "single" workshare
			 */
			ASTNode parent = ompFor.parent();
			if (parent instanceof OmpParallelNode) {
				//System.out
				//		.println("OpenMP Transformer: eliminating parallel and for");

				// Remove "for" node from "omp for" node
				int forIndex = getChildIndex(ompFor, fln);
				assert forIndex != -1;
				ompFor.removeChild(forIndex);

				// Link "for" into the grand parent
				ASTNode grand = parent.parent();
				int parentIndex = getChildIndex(grand, parent);
				assert parentIndex != -1;
				grand.setChild(parentIndex, fln);
			} else {
				//System.out
				//		.println("OpenMP Transformer: replacing for with single workshare");

				int ompForIndex = getChildIndex(parent, ompFor);
				assert ompForIndex != -1;
				parent.removeChild(ompForIndex);

				// OmpNodeFactory ompFactory = new CommonOmpNodeFactory(new
				// CommonValueFactory(new CommonTypeFactory()));
				// List<CToken> singleBody = new ArrayList<CToken>();
				// Iterator<CToken> tokIt = ompFor.getTokens();
				// while (tokIt.hasNext()) {
				// singleBody.add(tokIt.next());
				//
				// }

				// OmpWorkshareNode single =
				// ompFactory.newWorkshareNode(ompFor.getSource(),
				// ompFor.getPragmaIdentifier(),
				// singleBody, ompFor.getToken(ompFor.getNumTokens()-1),
				// OmpWorkshareNodeKind.SINGLE);
				fln.parent().removeChild(fln.childIndex());
				OmpWorksharingNode single = nodeFactory.newOmpSingleNode(
						ompFor.getSource(), fln);

				// fln.parent().removeChild(fln.childIndex());
				// single.setStatementNode(fln);

				// Transfer private, firstprivate, copyprivate, and nowait
				// clauses to single
				single.setPrivateList(ompFor.privateList());
				single.setFirstprivateList(ompFor.firstprivateList());
				single.setCopyprivateList(ompFor.copyprivateList());
				single.setNowait(ompFor.nowait());

				parent.setChild(ompForIndex, single);
			}
		}
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
				if (privateIDs == null || !privateIDs.contains(idEnt)) {
					writeVars.add(idEnt);
				}
			} else if (lhs instanceof OperatorNode
					&& ((OperatorNode) lhs).getOperator() == Operator.SUBSCRIPT) {
				writeArrayRefs.add((OperatorNode) lhs);

			} else {
				//System.out.println("DependenceAnnotator found lhs:" + lhs);
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
			if (privateIDs == null || !privateIDs.contains(idEnt)) {
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
	 */
	private boolean hasArrayRefDependences(Set<OperatorNode> writes,
			Set<OperatorNode> reads) {
		for (OperatorNode w : writes) {
			if (! (w instanceof IdentifierExpressionNode));
				//System.out.println("Write of type:"+w);
			IdentifierExpressionNode baseWrite = (IdentifierExpressionNode) w
					.getArgument(0);

			for (OperatorNode r : reads) {
				IdentifierExpressionNode baseRead = (IdentifierExpressionNode) r
						.getArgument(0);

				if (baseWrite.getIdentifier().getEntity() == baseRead
						.getIdentifier().getEntity()) {
					// Need to check logical equality of these expressions
					if (!ExpressionEvaluator.isEqualIntExpr(w.getArgument(1),
							r.getArgument(1))) {
						return true;
					}
				}
			}
		}
		return false;
	}

}
