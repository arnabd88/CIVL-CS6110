package edu.udel.cis.vsl.civl.transform.common;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.AtomicNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CompoundStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ExpressionStatementNode;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.parse.IF.CParser;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.civl.transform.IF.SvcompTransformer;

public class SvcompWorker extends BaseWorker {

	private final static String VERIFIER_ATOMIC = "__VERIFIER_atomic";

	private final static String VERIFIER_ATOMIC_BEGIN = "__VERIFIER_atomic_begin";

	private final static String VERIFIER_ATOMIC_END = "__VERIFIER_atomic_end";

	private final static String VERIFIER_NONDET_INT = "__VERIFIER_nondet_int";

	private final static String VERIFIER_NONDET_UINT = "__VERIFIER_nondet_uint";

	private final static String NONDET_INT = "int";

	private final static String BOUND = "bound";

	private List<VariableDeclarationNode> nondet_int_variable_declarations = new LinkedList<>();

	public SvcompWorker(ASTFactory astFactory) {
		super(SvcompTransformer.LONG_NAME, astFactory);
		this.identifierPrefix = "_" + SvcompTransformer.CODE;
	}

	@Override
	public AST transform(AST ast) throws SyntaxException {
		SequenceNode<BlockItemNode> rootNode = ast.getRootNode();

		ast.release();
		this.processVerifierFunctions(rootNode);
		if (this.nondet_int_variable_declarations.size() > 0)
			rootNode = insert_input_variables(rootNode);
		this.completeSources(rootNode);
		ast = astFactory.newAST(rootNode, ast.getSourceFiles());
		// ast.prettyPrint(System.out, false);
		return ast;
	}

	private SequenceNode<BlockItemNode> insert_input_variables(
			SequenceNode<BlockItemNode> rootNode) {
		List<BlockItemNode> blockItems = new LinkedList<>();
		VariableDeclarationNode nondet_bound_var = this.variableDeclaration(
				this.identifierPrefix + "_" + NONDET_INT + "_" + BOUND,
				this.basicType(BasicTypeKind.INT));
		String nondet_bound_var_name = nondet_bound_var.getName();

		nondet_bound_var.getTypeNode().setInputQualified(true);
		blockItems.addAll(this.nondet_int_variable_declarations);

		// create the bound variable for nondet int
		blockItems.add(nondet_bound_var);
		// add upper bound variable and assumptions
		blockItems.add(this.assumeFunctionDeclaration(this.newSource("$assume",
				CParser.DECLARATION)));
		for (VariableDeclarationNode nondet_var : nondet_int_variable_declarations) {
			blockItems.add(this.assumeNode(this.nodeFactory.newOperatorNode(
					nondet_var.getSource(), Operator.LTE,
					this.identifierExpression(nondet_var.getName()),
					this.identifierExpression(nondet_bound_var_name))));
		}
		for (BlockItemNode item : rootNode) {
			if (item != null) {
				item.remove();
				blockItems.add(item);
			}
		}
		return this.nodeFactory.newTranslationUnitNode(rootNode.getSource(),
				blockItems);
	}

	private void processVerifierFunctions(SequenceNode<BlockItemNode> root) {
		for (BlockItemNode item : root) {
			if (item == null)
				continue;

			if (item instanceof FunctionDefinitionNode) {
				FunctionDefinitionNode funcDef = (FunctionDefinitionNode) item;

				if (!funcDef.getName().startsWith(VERIFIER_ATOMIC)) {
					// CompoundStatementNode body = funcDef.getBody();
					// BlockItemNode atomicStmt;
					//
					// body.remove();
					// atomicStmt = this.nodeFactory.newAtomicStatementNode(
					// body.getSource(), false, body);
					// body = this.nodeFactory.newCompoundStatementNode(
					// body.getSource(), Arrays.asList(atomicStmt));
					// funcDef.setBody(body);
					// } else {
					process_atomic_begin_end(funcDef.getBody());
				}
			}
			process_nondet_int(item);
		}
	}

	private void process_nondet_int(ASTNode node) {
		if (node instanceof FunctionCallNode) {
			FunctionCallNode callNode = (FunctionCallNode) node;

			if (this.is_callee_name_equals(callNode, VERIFIER_NONDET_INT)
					|| this.is_callee_name_equals(callNode,
							VERIFIER_NONDET_UINT)) {
				VariableDeclarationNode inputVar = this.variableDeclaration(
						this.newUniqueIdentifier(NONDET_INT),
						this.basicType(BasicTypeKind.INT));
				ExpressionNode inputVarID = this.identifierExpression(inputVar
						.getName());

				inputVar.getTypeNode().setInputQualified(true);
				this.nondet_int_variable_declarations.add(inputVar);
				callNode.parent().setChild(callNode.childIndex(), inputVarID);
				return;
			}
		}
		for (ASTNode child : node.children()) {
			if (child != null)
				process_nondet_int(child);
		}
	}

	private void process_atomic_begin_end(ASTNode node) {
		if (node instanceof CompoundStatementNode) {
			CompoundStatementNode body = (CompoundStatementNode) node;
			List<BlockItemNode> newItems = new LinkedList<>();
			int atomicCount = 0;
			List<BlockItemNode> atomicItems = new LinkedList<>();
			boolean changed = false;

			for (BlockItemNode item : body) {
				if (item instanceof ExpressionStatementNode) {
					ExpressionNode expression = ((ExpressionStatementNode) item)
							.getExpression();

					if (expression instanceof FunctionCallNode) {
						if (is_atomic_begin_call((FunctionCallNode) expression)) {
							atomicCount++;
							changed = true;
						} else if (is_atomic_end_call((FunctionCallNode) expression)) {
							atomicCount--;
							if (atomicCount == 0 && atomicItems.size() > 0) {
								this.releaseNodes(atomicItems);
								newItems.add(this.nodeFactory.newAtomicStatementNode(
										this.newSource("$atomic",
												CParser.ATOMIC),
										false,
										this.nodeFactory.newCompoundStatementNode(
												this.newSource(
														"body-of-atomic-begin-end",
														CParser.COMPOUND_STATEMENT),
												atomicItems)));
								atomicItems = new LinkedList<>();
							}
						} else {
							if (this.is_atomic_call((FunctionCallNode) expression)) {
								ASTNode parent = item.parent();
								int itemIndex = item.childIndex();
								AtomicNode atomicNode;

								item.remove();
								atomicNode = this.nodeFactory
										.newAtomicStatementNode(
												item.getSource(),
												false,
												nodeFactory
														.newCompoundStatementNode(
																item.getSource(),
																Arrays.asList(item)));
								parent.setChild(itemIndex, atomicNode);
								item = atomicNode;
							}
							if (atomicCount > 0)
								atomicItems.add(item);
							else
								newItems.add(item);
						}
					} else {
						if (atomicCount > 0)
							atomicItems.add(item);
						else
							newItems.add(item);
					}
				} else {
					process_atomic_begin_end(item);
					if (atomicCount > 0)
						atomicItems.add(item);
					else
						newItems.add(item);
				}
			}
			if (changed) {
				this.releaseNodes(newItems);

				CompoundStatementNode newBody = this.nodeFactory
						.newCompoundStatementNode(body.getSource(), newItems);

				body.parent().setChild(body.childIndex(), newBody);
			}
		} else {
			for (ASTNode child : node.children()) {
				if (child == null)
					continue;
				process_atomic_begin_end(child);
			}
		}
	}

	// private void process_atomic_begin_end_work()

	private boolean is_atomic_call(FunctionCallNode call) {
		ExpressionNode function = call.getFunction();

		if (function instanceof IdentifierExpressionNode) {
			String name = ((IdentifierExpressionNode) function).getIdentifier()
					.name();

			if (name.startsWith(VERIFIER_ATOMIC))
				return true;
		}
		return false;
	}

	private boolean is_atomic_begin_call(FunctionCallNode call) {
		return this.is_callee_name_equals(call, VERIFIER_ATOMIC_BEGIN);
	}

	private boolean is_atomic_end_call(FunctionCallNode call) {
		return this.is_callee_name_equals(call, VERIFIER_ATOMIC_END);
	}

}
