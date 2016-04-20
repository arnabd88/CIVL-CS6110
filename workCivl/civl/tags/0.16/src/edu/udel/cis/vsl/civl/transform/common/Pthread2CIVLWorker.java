package edu.udel.cis.vsl.civl.transform.common;

import java.util.ArrayList;
import java.util.Arrays;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.ExternalDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode.ExpressionKind;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.label.LabelNode;
import edu.udel.cis.vsl.abc.ast.node.IF.label.OrdinaryLabelNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.AtomicNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CompoundStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ExpressionStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.LabeledStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ReturnNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.FunctionTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.PointerTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode.TypeNodeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.parse.IF.CParser;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;

//TODO: add arguments to pthread_exit();

public class Pthread2CIVLWorker extends BaseWorker {

	private final static String PTHREAD_CREATE = "pthread_create";

	private final static String PTHREAD_EXIT = "pthread_exit";

	private final static String PTHREAD_EXIT_NEW = "_pthread_exit";

	private final static String PTHREAD_FREE_POOL = "_free_pool";

	private final static String PTHREAD_POOL = "_pool";

	private final static String ERROR = "ERROR";

	private final static String VERIFIER_NONDET_UINT = "__VERIFIER_nondet_uint";

	private final static String VERIFIER_NONDET_INT = "__VERIFIER_nondet_int";

	private final static String VERIFIER_ASSUME = "__VERIFIER_assume";

	private final static String VERIFIER_ASSERT = "__VERIFIER_assert";

	private final static String VERIFIER_ATOMIC = "__VERIFIER_atomic";

	private int numberOfNondetCall = 0;

	/* **************************** Instance Fields ************************* */

	private ArrayList<String> funcList = new ArrayList<String>();

	// private boolean isSvComp = true;

	/* ****************************** Constructor ************************** */
	/**
	 * Creates a new instance of MPITransformer.
	 * 
	 * @param astFactory
	 *            The ASTFactory that will be used to create new nodes.
	 */
	public Pthread2CIVLWorker(ASTFactory astFactory) {
		super("PthreadToCIVLTransformer", astFactory);
	}

	/* *************************** Private Methods ************************* */

	private void processRoot(ASTNode root) throws SyntaxException {
		functionList(root);
		for (ASTNode node : root.children()) {
			if (node == null)
				continue;
			if (node instanceof FunctionDefinitionNode) {
				// if (config.svcomp()) {
				process_VERIFIER_function_calls((FunctionDefinitionNode) node);
				// }
				process_pthread_exits((FunctionDefinitionNode) node, funcList);
			} else if (/*
						 * config.svcomp() &&
						 */node instanceof FunctionDeclarationNode) {
				process_VERIFIER_functions((FunctionDeclarationNode) node);
			}
		}
		// if (config.svcomp())
		translateNode(root);
	}

	private void process_VERIFIER_function_calls(FunctionDefinitionNode node)
			throws SyntaxException {
		process_VERIFIER_function_call_worker(node);
	}

	/**
	 * Transforms VERIFIER functions into their corresponding counterparts:
	 * VERIFIER_nondet_int: abstract integer function VERIFIER_atomic: atomic
	 * function
	 * 
	 * @param node
	 *            ASTNode to be be checked for a VERIFIER
	 * 
	 */
	private void process_VERIFIER_function_call_worker(ASTNode node)
			throws SyntaxException {
		if (node instanceof FunctionCallNode) {
			FunctionCallNode funcCall = (FunctionCallNode) node;
			ExpressionNode function = funcCall.getFunction();

			if (function.expressionKind() == ExpressionKind.IDENTIFIER_EXPRESSION) {
				IdentifierExpressionNode funcName = (IdentifierExpressionNode) function;
				String name = funcName.getIdentifier().name();

				if (name.equals(VERIFIER_NONDET_INT)
						|| name.equals(VERIFIER_NONDET_UINT)) {
					ExpressionNode newArg = nodeFactory.newIntegerConstantNode(
							funcName.getSource(),
							String.valueOf(numberOfNondetCall));

					this.numberOfNondetCall++;
					funcCall.setArguments(nodeFactory.newSequenceNode(
							funcName.getSource(), "Actual Arguments",
							Arrays.asList(newArg)));
				}
			}
		} else if (node instanceof FunctionDefinitionNode) {
			IdentifierNode functionName = ((FunctionDefinitionNode) node)
					.getIdentifier();
			if (functionName.name().startsWith(VERIFIER_ATOMIC)) {
				CompoundStatementNode tmp = ((FunctionDefinitionNode) node)
						.getBody().copy();
				Source source = tmp.getSource();
				AtomicNode newAtomicBlock = nodeFactory.newAtomicStatementNode(
						source, false, tmp);
				CompoundStatementNode block = nodeFactory
						.newCompoundStatementNode(source,
								Arrays.asList((BlockItemNode) newAtomicBlock));
				((FunctionDefinitionNode) node).setBody(block);
			}
			for (ASTNode child : node.children()) {
				if (child != null)
					process_VERIFIER_function_call_worker(child);
			}
		} else {
			for (ASTNode child : node.children()) {
				if (child != null)
					process_VERIFIER_function_call_worker(child);
			}
		}
	}

	/**
	 * Inserts an abstract function node in place of VERIFIER_nondet_int
	 * 
	 * @param function
	 *            Node to be checked and converted for VERIFIER function
	 * 
	 */
	private void process_VERIFIER_functions(FunctionDeclarationNode function) {
		IdentifierNode functionName = function.getIdentifier();

		if (functionName.name().equals(VERIFIER_NONDET_UINT)
				|| functionName.name().equals(VERIFIER_NONDET_INT)) {
			FunctionTypeNode funcTypeNode = function.getTypeNode();
			FunctionDeclarationNode abstractNode;

			funcTypeNode = nodeFactory
					.newFunctionTypeNode(
							funcTypeNode.getSource(),
							funcTypeNode.getReturnType().copy(),
							nodeFactory.newSequenceNode(this.newSource(
									"formal parameter declarations of "
											+ functionName.name(),
									CParser.DECLARATION_LIST),
									"Formal Parameters",
									Arrays.asList(this.variableDeclaration(
											"seed",
											this.basicType(BasicTypeKind.INT)))),
							false);
			abstractNode = nodeFactory.newAbstractFunctionDefinitionNode(
					function.getSource(), function.getIdentifier().copy(),
					funcTypeNode, null, 0);
			function.parent().setChild(function.childIndex(), abstractNode);
		}
	}

	/**
	 * Translates nodes if they meet one of various specific cases
	 * 
	 * @param node
	 *            Node to be translated
	 * 
	 */
	private void translateNode(ASTNode node) {
		if (node instanceof LabeledStatementNode) {
			LabeledStatementNode labelStatement = (LabeledStatementNode) node;
			LabelNode labelNode = labelStatement.getLabel();

			if (labelNode instanceof OrdinaryLabelNode) {
				OrdinaryLabelNode label = (OrdinaryLabelNode) labelNode;
				String name = label.getName();
				if (name.equals(ERROR))
					labelStatement.setChild(1,
							this.assertFalse(labelStatement.getSource()));
			}
		} else if (node instanceof ExpressionStatementNode) {
			ExpressionNode expression = ((ExpressionStatementNode) node)
					.getExpression();
			StatementNode newStatementNode = null;

			if (expression.expressionKind() == ExpressionKind.FUNCTION_CALL) {
				FunctionCallNode functionCall = (FunctionCallNode) expression;
				ExpressionNode functionName = functionCall.getFunction();

				if (functionName.expressionKind() == ExpressionKind.IDENTIFIER_EXPRESSION) {
					String name = ((IdentifierExpressionNode) functionName)
							.getIdentifier().name();

					switch (name) {
					case VERIFIER_ASSERT:
						newStatementNode = this.assertNode(functionCall
								.getSource(), functionCall.getArgument(0)
								.copy());
						break;
					case VERIFIER_ASSUME:
						newStatementNode = this.assumeNode(functionCall
								.getArgument(0).copy());
						break;
					default:
					}
				}
				if (newStatementNode != null)
					node.parent().setChild(node.childIndex(), newStatementNode);
			}
		} else
			for (ASTNode child : node.children())
				if (child != null)
					this.translateNode(child);
	}

	private StatementNode assumeNode(ExpressionNode expression) {
		return nodeFactory.newAssumeNode(
				this.newSource("assumption", CParser.ASSUME), expression);
	}

	private StatementNode assertNode(Source mySource, ExpressionNode expression) {
		return nodeFactory.newAssertNode(
				this.newSource("assertion", CParser.ASSERT), expression, null);
		// FunctionCallNode functionCall =
		// nodeFactory.newFunctionCallNode(source,
		// this.identifierExpression(mySource, ASSERT),
		// Arrays.asList(expression), null);
		//
		// return nodeFactory.newExpressionStatementNode(functionCall);
	}

	/*
	 * private StatementNode whenNode(Source mySource, ExpressionNode
	 * expression) { return nodeFactory.newWhenNode(mySource, expression,
	 * nodeFactory.newNullStatementNode(mySource)); }
	 */
	/**
	 * Creates an assertFalse StatementNode
	 * 
	 * @param mySource
	 * 
	 * @return
	 */
	private StatementNode assertFalse(Source mySource) {
		ExpressionNode falseExpression = this.booleanConstant(false);

		return assertNode(mySource, falseExpression);
	}

	private void process_pthread_exits(FunctionDefinitionNode function,
			ArrayList<String> threadList) throws SyntaxException {
		String name = function.getName();
		TypeNode returnType = function.getTypeNode().getReturnType();

		if (name.equals("main")) {
			process_pthread_exit(function, true);
			ExpressionNode ZERO = this.integerConstant(0);

			function.getBody().addSequenceChild(
					nodeFactory.newReturnNode(
							this.newSource("return statement", CParser.RETURN),
							ZERO));
			freePoolBeforeMainReturn(function);
			return;

		}
		if (this.isVoidPointer(returnType) && threadList.contains(name)) {
			if (function.getTypeNode().getParameters().numChildren() == 0) {
				function.getTypeNode().setParameters(
						nodeFactory.newSequenceNode(this.newSource(
								"parameter declaration of "
										+ function.getName(),
								CParser.DECLARATION_LIST), "parameters", Arrays
								.asList(this.variableDeclaration("arg",
										nodeFactory.newPointerTypeNode(this
												.newSource("type void *",
														CParser.TYPE), this
												.voidType())))));
			}
			ExpressionNode nullNode = nodeFactory.newCastNode(
					this.newSource("cast expression", CParser.CAST),
					nodeFactory.newPointerTypeNode(
							this.newSource("type void *", CParser.TYPE),
							this.voidType()), this.integerConstant(0));
			ExpressionNode isMainArg = this.booleanConstant(false);
			FunctionCallNode newPthreadExit = nodeFactory.newFunctionCallNode(
					this.newSource("function call " + PTHREAD_EXIT_NEW,
							CParser.CALL), this
							.identifierExpression(PTHREAD_EXIT_NEW), Arrays
							.asList(nullNode, isMainArg), null);
			StatementNode pthreadExit = nodeFactory
					.newExpressionStatementNode(newPthreadExit);
			function.getBody().addSequenceChild(pthreadExit);
			process_pthread_exit(function, false);
		}
	}

	/**
	 * In main(), translate pthread_exit(arg) to pthread_exit(arg, true); in
	 * other function, translate pthread_exit(arg) to pthread_exit(arg, false).
	 * 
	 * @param function
	 */
	private void process_pthread_exit(FunctionDefinitionNode function,
			boolean isMain) {
		process_pthread_exit_worker(function, isMain);
	}

	private void process_pthread_exit_worker(ASTNode node, boolean isMain) {
		for (ASTNode child : node.children()) {
			if (child == null)
				continue;
			if (child instanceof FunctionCallNode) {
				FunctionCallNode funcCall = (FunctionCallNode) child;
				ExpressionNode funcName = funcCall.getFunction();

				if (funcName instanceof IdentifierExpressionNode) {
					IdentifierExpressionNode name = (IdentifierExpressionNode) funcName;
					String nameString = name.getIdentifier().name();

					if (nameString.equals(PTHREAD_EXIT)) {
						ExpressionNode isMainArg = this.booleanConstant(isMain);
						ExpressionNode oldArg = funcCall.getArgument(0);
						SequenceNode<ExpressionNode> newArgs;

						name.getIdentifier().setName(PTHREAD_EXIT_NEW);
						oldArg.parent().removeChild(oldArg.childIndex());
						newArgs = nodeFactory.newSequenceNode(
								this.newSource("actual parameter list of "
										+ nameString, CParser.ARGUMENT_LIST),
								"Actual parameters",
								Arrays.asList(oldArg, isMainArg));
						funcCall.setArguments(newArgs);
					}
				}
			} else if (child instanceof ReturnNode && !isMain) {
				ExpressionNode isMainArg = this.booleanConstant(isMain);
				FunctionCallNode newPthreadExit = nodeFactory
						.newFunctionCallNode(this.newSource("function call of "
								+ PTHREAD_EXIT_NEW, CParser.CALL), this
								.identifierExpression(PTHREAD_EXIT_NEW), Arrays
								.asList(((ReturnNode) child).getExpression()
										.copy(), isMainArg), null);
				StatementNode pthreadExit = nodeFactory
						.newExpressionStatementNode(newPthreadExit);

				child.parent().setChild(child.childIndex(), pthreadExit);
			} else {
				process_pthread_exit_worker(child, isMain);
			}
		}
	}

	private void functionList(ASTNode root) {
		for (ASTNode node : root.children()) {
			if (node == null)
				continue;
			if (node instanceof FunctionCallNode) {
				FunctionCallNode funcCall = (FunctionCallNode) node;
				ExpressionNode funcName = funcCall.getFunction();
				if (funcName instanceof IdentifierExpressionNode) {
					IdentifierExpressionNode named = (IdentifierExpressionNode) funcName;
					String nameString = named.getIdentifier().name();
					if (nameString.equals(PTHREAD_CREATE)) {
						ExpressionNode arg = funcCall.getArgument(2);
						if (arg instanceof OperatorNode) {
							OperatorNode argOp = (OperatorNode) arg;
							IdentifierExpressionNode threadName = (IdentifierExpressionNode) argOp
									.getArgument(0);
							funcList.add(threadName.getIdentifier().name());
						} else {
							IdentifierExpressionNode threadName = (IdentifierExpressionNode) funcCall
									.getArgument(2);
							funcList.add(threadName.getIdentifier().name());
						}
					}
				}
			} else {
				functionList(node);
			}
		}
	}

	@SuppressWarnings("unused")
	private ReturnNode returnNull() throws SyntaxException {
		ExpressionNode nullNode = nodeFactory.newCastNode(
				this.newSource("cast expression", CParser.CAST),
				nodeFactory.newPointerTypeNode(
						this.newSource("type void *", CParser.TYPE),
						this.voidType()), this.integerConstant(0));

		return nodeFactory.newReturnNode(
				this.newSource("return statement", CParser.RETURN), nullNode);
	}

	private boolean isVoidPointer(TypeNode type) {
		if (type.kind() == TypeNodeKind.POINTER) {
			PointerTypeNode pointer = (PointerTypeNode) type;

			if (pointer.referencedType().kind() == TypeNodeKind.VOID)
				return true;
		}
		return false;
	}

	private void freePoolBeforeMainReturn(ASTNode node) {
		if (node instanceof ReturnNode) {
			BlockItemNode freePoolCall = freePoolCall();
			CompoundStatementNode compound;
			ASTNode parent = node.parent();
			int index = node.childIndex();

			parent.removeChild(index);
			compound = nodeFactory.newCompoundStatementNode(node.getSource(),
					Arrays.asList(freePoolCall, (ReturnNode) node));
			parent.setChild(index, compound);
		} else
			for (ASTNode child : node.children())
				if (child != null)
					freePoolBeforeMainReturn(child);
	}

	private StatementNode freePoolCall() {
		ExpressionNode poolArg = nodeFactory.newOperatorNode(
				this.newSource("address-of expression", CParser.EXPR),
				Operator.ADDRESSOF,
				Arrays.asList(identifierExpression(PTHREAD_POOL)));
		FunctionCallNode funcCall = nodeFactory.newFunctionCallNode(this
				.newSource("function call " + PTHREAD_FREE_POOL, CParser.CALL),
				this.identifierExpression(PTHREAD_FREE_POOL), Arrays
						.asList(poolArg), null);

		return nodeFactory.newExpressionStatementNode(funcCall);
	}

	/* ********************* Methods From BaseTransformer ****************** */

	@Override
	public AST transform(AST ast) throws SyntaxException {
		SequenceNode<ExternalDefinitionNode> root = ast.getRootNode();

		assert this.astFactory == ast.getASTFactory();
		assert this.nodeFactory == astFactory.getNodeFactory();
		ast.release();
		processRoot(root);
		this.completeSources(root);
		return astFactory.newAST(root, ast.getSourceFiles());
	}
}
