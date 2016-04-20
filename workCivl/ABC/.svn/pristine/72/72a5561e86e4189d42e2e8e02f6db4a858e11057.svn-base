package edu.udel.cis.vsl.abc.analysis.common;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import edu.udel.cis.vsl.abc.analysis.IF.Analyzer;
import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.entity.IF.Function;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.NodeFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.AtomicNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ChooseStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CivlForNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CompoundStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.DeclarationListNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ExpressionStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ForLoopNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.GotoNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.IfNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.JumpNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.LabeledStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.LoopNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.NullStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ReturnNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.SwitchNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.WhenNode;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;

/**
 * Given an AST determines successor/predecessor relationships among statements.
 * 
 * The strategy for building the CF edges is as follows: - top down visit of AST
 * for each method definition - construct control flow relation as you move down
 * - note that this relation is incorrect, but it records successors of compound
 * statements - within a compound statement, when you want to connect to your
 * successor you - use the enclosing compound statements successor - delete
 * their old successor
 * 
 * We could follow the model of the CallAnalyzer and extend the AST with
 * pred/succ functions that return sets of statements where "null" means that no
 * information has been computed. With this approach multiple calls to compute
 * ControlFlow for parts of the AST can be made and the results will persist for
 * the life of the AST.
 * 
 * There should be no reason why this code does not operate on a whole program.
 * We just need to visit the substructure down to the level of the method body,
 * then switch over to the control flow collector routines.
 * 
 * Add to other interfaces: Functions : entryStmt Statements : preds/succs
 * 
 * @author dwyer
 * 
 */
public class ControlFlowAnalyzer implements Analyzer {
	Map<StatementNode, Set<StatementNode>> successors = new HashMap<StatementNode, Set<StatementNode>>();
	Map<StatementNode, Set<StatementNode>> predecessors = new HashMap<StatementNode, Set<StatementNode>>();

	/*
	 * For a method: (1) The body of the definition is the entry statement (2) A
	 * new dummy null statement is the distinguished exit statement
	 */
	StatementNode exitStmt = null;
	StatementNode currStmt = null;

	AST currentAST;

	void addEdge(StatementNode n1, StatementNode n2) {
		Set<StatementNode> succs = successors.get(n1);
		if (succs == null) {
			succs = new HashSet<StatementNode>();
			successors.put(n1, succs);
		}
		succs.add(n2);

		Set<StatementNode> preds = predecessors.get(n2);
		if (preds == null) {
			preds = new HashSet<StatementNode>();
			predecessors.put(n2, preds);
		}
		preds.add(n2);
	}

	StatementNode soleSuccessor(StatementNode node) {
		Set<StatementNode> succs = successors.get(node);
		assert succs.size() == 1;
		return succs.iterator().next();
	}

	@SuppressWarnings("unused")
	private void collectProgram(ASTNode node) {
		if (node instanceof FunctionDefinitionNode) {
			collectFunctionDefinitionNode((FunctionDefinitionNode) node);
		} else {
			for (ASTNode child : node.children()) {
				if (child != null)
					collectProgram(child);
			}
		}
	}

	private void collectFunctionDefinitionNode(FunctionDefinitionNode funNode) {
		NodeFactory nf = currentAST.getASTFactory().getNodeFactory();
		exitStmt = nf.newNullStatementNode(funNode.getBody().getSource());

		addEdge(funNode.getBody(), exitStmt);

		collectCompoundStatementNode(funNode.getBody());

		// link exit into the AST so that it persists
	}

	/*
	 * Dispatch to statement-specific control flow edge building methods
	 */
	private void collectStatement(ASTNode node) {
		if (node instanceof AtomicNode) {
			collectAtomicNode(node);

		} else if (node instanceof ChooseStatementNode) {
			collectChooseStatementNode(node);

		} else if (node instanceof CompoundStatementNode) {
			collectCompoundStatementNode((CompoundStatementNode) node);

		} else if (node instanceof DeclarationListNode) {
			collectDeclarationListNode(node);

		} else if (node instanceof ExpressionStatementNode) {
			collectExpressionStatementNode(node);

		} else if (node instanceof ForLoopNode) {
			collectForLoopNode(node);

		} else if (node instanceof GotoNode) {
			collectGotoNode(node);

		} else if (node instanceof IfNode) {
			collectIfNode((IfNode) node);

		} else if (node instanceof JumpNode) {
			collectJumpNode(node);

		} else if (node instanceof LabeledStatementNode) {
			collectLabeledStatementNode(node);

		} else if (node instanceof LoopNode) {
			collectLoopNode(node);

		} else if (node instanceof ReturnNode) {
			collectReturnNode(node);

		} else if (node instanceof SwitchNode) {
			collectSwitchNode(node);

		} else if (node instanceof WhenNode) {
			collectWhenNode(node);

		} else if (node instanceof NullStatementNode) {
			collectNullStatementNode(node);

		} else if (node instanceof CivlForNode) {
			collectCivlForNode(node);

		} else {
			assert false : "Unhandled statement type:" + node;
		}

		for (ASTNode child : node.children()) {
			if (child != null)
				collectStatement(child);
		}
	}

	// add functions to build edges for each type of statement
	private void collectCompoundStatementNode(CompoundStatementNode node) {
		// Pass at this level to construct sequential control flow
		for (BlockItemNode item : node) {
			if (item instanceof StatementNode) {
				StatementNode theStmt = (StatementNode) item;
				Set<StatementNode> succs = new HashSet<StatementNode>();
				Set<StatementNode> preds = new HashSet<StatementNode>();
				succs.add(theStmt);
				preds.add(currStmt);
				successors.put(currStmt, succs);
				predecessors.put(theStmt, preds);
				currStmt = theStmt;
			}
		}

		// recurse to build control flow based on statement structure
		for (BlockItemNode item : node) {
			collectStatement(item);
		}

	}

	private void collectChooseStatementNode(ASTNode node) {
	}

	private void collectDeclarationListNode(ASTNode node) {
	}

	private void collectExpressionStatementNode(ASTNode node) {
	}

	private void collectForLoopNode(ASTNode node) {
	}

	private void collectLoopNode(ASTNode node) {
	}

	private void collectGotoNode(ASTNode node) {
	}

	private void collectIfNode(IfNode node) {
		// Record the successor of the if
		StatementNode ifSucc = soleSuccessor(node);

		StatementNode trueStatement = node.getTrueBranch();
		StatementNode falseStatement = node.getFalseBranch();
		Set<StatementNode> succs = new HashSet<StatementNode>();
		Set<StatementNode> predsTrue = new HashSet<StatementNode>();
		Set<StatementNode> predsFalse = new HashSet<StatementNode>();

		succs.add(trueStatement);
		succs.add(falseStatement);
		predsTrue.add(node);
		predsFalse.add(node);

		successors.put(currStmt, succs);
		predecessors.put(trueStatement, predsTrue);
		predecessors.put(falseStatement, predsFalse);

		collectStatement(trueStatement);
		collectStatement(falseStatement);

		// Remove dummy successor
		Set<StatementNode> nodeSuccs = successors.get(node);
		nodeSuccs.remove(ifSucc);
	}

	private void collectLabeledStatementNode(ASTNode node) {
	}

	private void collectReturnNode(ASTNode node) {
	}

	private void collectSwitchNode(ASTNode node) {
	}

	private void collectWhenNode(ASTNode node) {
	}

	private void collectAtomicNode(ASTNode node) {
	}

	private void collectJumpNode(ASTNode node) {
	}

	private void collectNullStatementNode(ASTNode node) {
	}

	private void collectCivlForNode(ASTNode node) {
	}

	@Override
	public void clear(AST unit) {
		successors.clear();
		predecessors.clear();
		clearNode(unit.getRootNode());
	}

	private void clearNode(ASTNode node) {
		if (node != null) {
			if (node instanceof FunctionDefinitionNode) {
				Function f = ((FunctionDefinitionNode) node).getEntity();
				if (f != null) {
					Set<Function> callers = f.getCallers();
					if (callers != null)
						callers.clear();
					Set<Function> callees = f.getCallees();
					if (callees != null)
						callees.clear();
				}
			}
			for (ASTNode child : node.children()) {
				clearNode(child);
			}
		}
	}

	@Override
	public void analyze(AST unit) throws SyntaxException {
		collectStatement(unit.getRootNode());
	}

	static private Set<Function> seen;

	static public void printControlFlowGraph(AST unit) {
		System.out.println(unit.getMain().getName());
		seen = new HashSet<Function>();
		seen.add(unit.getMain());
		printControlFlowGraphNode(unit.getMain(), " ");
	}

	static private void printControlFlowGraphNode(Function f, String pre) {
		for (Function callee : f.getCallees()) {
			System.out.print(pre + callee.getName() + " [");
			for (Function caller : callee.getCallers()) {
				System.out.print(" " + caller.getName());
			}
			System.out.println(" ]");
			if (!seen.contains(callee)) {
				seen.add(callee);
				printControlFlowGraphNode(callee, pre + " ");
				seen.remove(callee);
			} else {
				System.out.println(pre + " <recursion>");
			}
		}
	}

}
