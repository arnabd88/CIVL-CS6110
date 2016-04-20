package edu.udel.cis.vsl.civl.transform.common;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.CastNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode.ExpressionKind;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode;
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
import edu.udel.cis.vsl.abc.ast.type.IF.Type.TypeKind;
import edu.udel.cis.vsl.abc.parse.IF.CParser;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;

//TODO: add arguments to pthread_exit();

/**
 * TODO list all the transformation (e.g., pthread_create, pthread_exit to
 * _pthread_exit) with explanation of how it works and why it is necessary
 * 
 * @author zmanchun
 *
 */
public class Pthread2CIVLWorker extends BaseWorker {

	// private final static String PTHREAD_MUTEX_LOCK="pthread_mutex_lock";

	private final static String PTHREAD_POOL_TYPE = "$pthread_pool_t";

	static final String PTHREAD_MUTEX_LOCK = "pthread_mutex_lock";

	static final String PTHREAD_MUTEX_LOCK_NEW = "_pthread_mutex_lock";

	static final String PTHREAD_COND_WAIT = "pthread_cond_wait";

	static final String PTHREAD_COND_WAIT_NEW = "_pthread_cond_wait";

	final static String PTHREAD_POOL_CREATE = "$pthread_pool_create";

	final static String PTHREAD_GPOOL = "$pthread_gpool";

	private final static String PTHREAD_POOL = "$pthread_pool";

	// needs to go to MPI process scope
	final static String PTHREAD_CREATE = "pthread_create";

	private final static String PTHREAD_EXIT = "pthread_exit";

	final static String PTHREAD_EXIT_NEW = "_pthread_exit";

	private final static String PTHREAD_SELF = "pthread_self";

	final static String PTHREAD_SELF_NEW = "_pthread_self";

	// needs to go to MPI process scope
	final static String PTHREAD_EXIT_MAIN_NEW = "_pthread_exit_main";

	private final static String ERROR = "ERROR";

	private final static String VERIFIER_NONDET_UINT = "__VERIFIER_nondet_uint";

	private final static String VERIFIER_NONDET_INT = "__VERIFIER_nondet_int";

	private final static String VERIFIER_ASSUME = "__VERIFIER_assume";

	private final static String VERIFIER_ASSERT = "__VERIFIER_assert";

	private final static String VERIFIER_ATOMIC = "__VERIFIER_atomic";

	private int numberOfNondetCall = 0;

	private boolean exitMainDone = false;

	/* **************************** Instance Fields ************************* */

	private List<String> funcList = new ArrayList<>();

	// private FunctionDefinitionNode mainFunction;

	private Set<FunctionDefinitionNode> nonThreadFunctionsWtSyncCalls = new HashSet<>();

	private List<String> syncCallFunctionNames = new ArrayList<>();

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
		this.identifierPrefix = "$pthreads_";
	}

	/* *************************** Private Methods ************************* */

	private VariableDeclarationNode pthread_pool_declaration(
			boolean wtInitializer) {
		TypeNode pthreadPoolType;
		List<ExpressionNode> pthreadPoolCreateArgs;
		ExpressionNode pthreadPoolCreate;

		pthreadPoolType = nodeFactory.newTypedefNameNode(nodeFactory
				.newIdentifierNode(this.newSource("$phtread_pool_t type",
						CParser.IDENTIFIER), PTHREAD_POOL_TYPE), null);
		if (wtInitializer) {
			pthreadPoolCreateArgs = new ArrayList<>(2);
			pthreadPoolCreateArgs.add(this.hereNode());
			pthreadPoolCreateArgs.add(this.identifierExpression(PTHREAD_GPOOL));
			pthreadPoolCreate = nodeFactory.newFunctionCallNode(this.newSource(
					"function call " + PTHREAD_POOL_CREATE, CParser.CALL), this
					.identifierExpression(PTHREAD_POOL_CREATE),
					pthreadPoolCreateArgs, null);
			return this.variableDeclaration(PTHREAD_POOL, pthreadPoolType,
					pthreadPoolCreate);
		} else
			return this.variableDeclaration(PTHREAD_POOL, pthreadPoolType);
	}

	/**
	 * TODO javadocs
	 * 
	 * @param root
	 * @throws SyntaxException
	 */
	private void processRoot(ASTNode root) throws SyntaxException {
		functionList(root);
		for (ASTNode node : root.children()) {
			if (node == null)
				continue;
			if (node instanceof FunctionDefinitionNode) {
				// if (config.svcomp()) {
				process_thread_functions((FunctionDefinitionNode) node);
				process_VERIFIER_function_calls((FunctionDefinitionNode) node);
				// }
				process_pthread_exits((FunctionDefinitionNode) node, funcList);
				process_pthread_sync_calls((FunctionDefinitionNode) node);
			} else if (/*
						 * config.svcomp() &&
						 */node instanceof FunctionDeclarationNode) {
				process_VERIFIER_functions((FunctionDeclarationNode) node);
			}
		}
		process_nonThread_functions_wt_syncCalls();
		if (this.syncCallFunctionNames.size() > 0)
			process_function_call_of_functionsWtSyncCalls(root);
		// if (config.svcomp())
		translateNode(root);
	}

	private void process_function_call_of_functionsWtSyncCalls(ASTNode root) {
		for (ASTNode node : root.children()) {
			if (node == null)
				continue;
			if (node instanceof FunctionCallNode) {
				FunctionCallNode call = (FunctionCallNode) node;
				ExpressionNode function = call.getFunction();

				if (function instanceof IdentifierExpressionNode) {
					String funcName = ((IdentifierExpressionNode) function)
							.getIdentifier().name();

					if (this.syncCallFunctionNames.contains(funcName)) {
						call.getArguments().addSequenceChild(
								this.identifierExpression(PTHREAD_POOL));
					}
				}
			}
			process_function_call_of_functionsWtSyncCalls(node);
		}
	}

	private void process_nonThread_functions_wt_syncCalls() {
		Iterator<FunctionDefinitionNode> iterator = this.nonThreadFunctionsWtSyncCalls
				.iterator();

		while (iterator.hasNext())
			process_sync_call_function(iterator.next());
	}

	/**
	 * modify the function definition to take an extra argument: $pthread_pool_t
	 * pthread_pool
	 * 
	 * @param funcDef
	 */
	private void process_sync_call_function(FunctionDefinitionNode funcDef) {
		FunctionTypeNode funcType = funcDef.getTypeNode();
		VariableDeclarationNode pthread_pool_param = this
				.pthread_pool_declaration(false);

		funcType.getParameters().addSequenceChild(pthread_pool_param);
		if (!this.funcList.contains(funcDef.getName()))
			syncCallFunctionNames.add(funcDef.getName());
	}

	private void process_pthread_sync_calls(FunctionDefinitionNode node) {
		process_pthread_sync_calls(node, node);
	}

	private void process_pthread_sync_calls(FunctionDefinitionNode funcDef,
			ASTNode node) {
		for (ASTNode child : node.children()) {
			if (child == null)
				continue;
			if (child instanceof FunctionCallNode) {
				process_pthread_sync_call(funcDef, (FunctionCallNode) child);
			}
			process_pthread_sync_calls(funcDef, child);
		}
	}

	/**
	 * transforms pthread_mutex_lock(mutex) to pthread_mutex_lock(mutex,
	 * $pthread_pool) and similar for pthread_cond_wait();
	 * 
	 * @param node
	 */
	private void process_pthread_sync_call(FunctionDefinitionNode funcDef,
			FunctionCallNode node) {
		ExpressionNode function = node.getFunction();
		boolean hasSyncCall = false;

		if (function instanceof IdentifierExpressionNode) {
			String funcName = ((IdentifierExpressionNode) function)
					.getIdentifier().name();

			if (funcName.equals(PTHREAD_MUTEX_LOCK)
					|| funcName.equals(PTHREAD_COND_WAIT) || funcName.equals(PTHREAD_SELF)) {
				hasSyncCall = true;
				((IdentifierExpressionNode) function).getIdentifier().setName(
						"_" + funcName);
			}
			if (hasSyncCall) {
				node.getArguments().addSequenceChild(
						this.identifierExpression(PTHREAD_POOL));
				if (!this.funcList.contains(funcDef.getName()))
					nonThreadFunctionsWtSyncCalls.add(funcDef);
			}
		}
	}

	/**
	 * Insert pthread pool creation at the beginning of pthread functions
	 * 
	 * @param node
	 */
	private void process_thread_functions(FunctionDefinitionNode node) {
		String name = node.getName();

		if (this.funcList.contains(name)) {
			CompoundStatementNode body = node.getBody();
			List<BlockItemNode> newBodyNodes = new LinkedList<>();
			VariableDeclarationNode pthreadPoolVar = this
					.pthread_pool_declaration(true);

			body.remove();
			newBodyNodes.add(pthreadPoolVar);
			newBodyNodes.add(body);
			node.setBody(this.nodeFactory.newCompoundStatementNode(
					body.getSource(), newBodyNodes));
		}
	}

	/**
	 * Processes function calls starting with __VERIFIER_, which are special
	 * functions of the SV-COMP.
	 * 
	 * @param node
	 *            The function definition node whose body is to be searched for
	 *            __VERIFIER_ calls for transformation.
	 * @throws SyntaxException
	 */
	private void process_VERIFIER_function_calls(FunctionDefinitionNode node)
			throws SyntaxException {
		process_VERIFIER_function_call_worker(node);
	}

	/**
	 * TODO documentation about VERIFIER_nondet_int and VERIFIER_atomic
	 * Transforms __VERIFIER_ function calls into their corresponding
	 * counterparts:
	 * <ul>
	 * <li>VERIFIER_nondet_int: abstract integer function</li>
	 * <li>VERIFIER_atomic: atomic function</li>
	 * </ul>
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
		return nodeFactory.newExpressionStatementNode(this.functionCall(
				this.newSource("assumption", CParser.ASSUME), ASSUME,
				Arrays.asList(expression)));
	}

	private StatementNode assertNode(Source mySource, ExpressionNode expression) {
		return nodeFactory.newExpressionStatementNode(this.functionCall(
				this.newSource("assertion", CParser.ASSERT), ASSERT,
				Arrays.asList(expression)));
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
	 * Creates a StatementNode for error report: $assert $false.
	 * 
	 * @param mySource
	 * 
	 * @return
	 */
	private StatementNode assertFalse(Source mySource) {
		ExpressionNode falseExpression = this.booleanConstant(false);

		return assertNode(mySource, falseExpression);
	}

	/**
	 * TODO javadocs
	 * 
	 * @param function
	 * @param threadList
	 * @throws SyntaxException
	 */
	private void process_pthread_exits(FunctionDefinitionNode function,
			List<String> threadList) throws SyntaxException {
		String name = function.getName();
		TypeNode returnType = function.getTypeNode().getReturnType();
		boolean isMain = name.equals("main");

		if (name.equals("main")) {
			ExpressionNode ZERO = this.integerConstant(0);
			if (!hasReturn(function)) {
				if (returnType.getType().kind() == TypeKind.VOID)
					function.getBody().addSequenceChild(
							nodeFactory.newReturnNode(this.newSource(
									"return statement", CParser.RETURN), null));
				else
					function.getBody().addSequenceChild(
							nodeFactory.newReturnNode(this.newSource(
									"return statement", CParser.RETURN), ZERO));
			}
			process_pthread_exit(function, true);
			// return;
		}
		if ((this.isVoidPointerType(returnType) && threadList.contains(name))) {
			String pthread_exit_name = isMain ? PTHREAD_EXIT_MAIN_NEW
					: PTHREAD_EXIT_NEW;

			if (!isMain
					&& function.getTypeNode().getParameters().numChildren() == 0) {
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
			// ExpressionNode isMainArg = this.booleanConstant(false);
			FunctionCallNode newPthreadExit = nodeFactory.newFunctionCallNode(
					this.newSource("function call " + pthread_exit_name,
							CParser.CALL),
					this.identifierExpression(pthread_exit_name),
					isMain ? Arrays.asList(nullNode) : Arrays.asList(nullNode,
							this.identifierExpression(this.newSource(
									PTHREAD_POOL, CParser.IDENTIFIER),
									PTHREAD_POOL)), null);
			StatementNode pthreadExit = nodeFactory
					.newExpressionStatementNode(newPthreadExit);
			function.getBody().addSequenceChild(pthreadExit);
			process_pthread_exit(function, isMain);
		}
	}

	/**
	 * In main(), translate pthread_exit(arg) to pthread_exit(arg, true); in
	 * other function, translate pthread_exit(arg) to pthread_exit(arg, false).
	 * 
	 * @param function
	 * @throws SyntaxException
	 */
	private void process_pthread_exit(FunctionDefinitionNode function,
			boolean isMain) throws SyntaxException {
		process_pthread_exit_worker(function, isMain);
	}

	/**
	 * TODO javadoc
	 * 
	 * @param node
	 * @param isMain
	 * @throws SyntaxException
	 */
	private void process_pthread_exit_worker(ASTNode node, boolean isMain)
			throws SyntaxException {
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
						// ExpressionNode isMainArg =
						// this.booleanConstant(isMain);
						ExpressionNode oldArg = funcCall.getArgument(0);
						SequenceNode<ExpressionNode> newArgs;

						if (!isMain) {
							name.getIdentifier().setName(PTHREAD_EXIT_NEW);
							oldArg.parent().removeChild(oldArg.childIndex());
							newArgs = nodeFactory
									.newSequenceNode(
											this.newSource(
													"actual parameter list of "
															+ nameString,
													CParser.ARGUMENT_LIST),
											"Actual parameters",
											Arrays.asList(
													oldArg,
													this.identifierExpression(
															this.newSource(
																	PTHREAD_POOL,
																	CParser.IDENTIFIER),
															PTHREAD_POOL)));
							funcCall.setArguments(newArgs);
						} else if (!exitMainDone) {
							this.exitMainDone = true;
							name.getIdentifier().setName(PTHREAD_EXIT_MAIN_NEW);
						}
					}
				}
			} else if (child instanceof ReturnNode
					&& (!isMain || !exitMainDone)) {
				// ExpressionNode isMainArg = this.booleanConstant(isMain);
				String pthread_exit_name = isMain ? PTHREAD_EXIT_MAIN_NEW
						: PTHREAD_EXIT_NEW;

				if (isMain)
					exitMainDone = true;
				FunctionCallNode newPthreadExit = nodeFactory
						.newFunctionCallNode(
								this.newSource("function call of "
										+ pthread_exit_name, CParser.CALL),
								this.identifierExpression(pthread_exit_name),
								isMain ? Arrays.asList((ExpressionNode) nodeFactory
										.newCastNode(this
												.newSource("cast expression",
														CParser.CAST),
												nodeFactory.newPointerTypeNode(
														this.newSource(
																"type void *",
																CParser.TYPE),
														this.voidType()), this
														.integerConstant(0))

								)
										: Arrays.asList(
												((ReturnNode) child)
														.getExpression().copy(),
												this.identifierExpression(
														this.newSource(
																PTHREAD_POOL,
																CParser.IDENTIFIER),
														PTHREAD_POOL)), null);
				StatementNode pthreadExit = nodeFactory
						.newExpressionStatementNode(newPthreadExit);

				child.parent().setChild(child.childIndex(), pthreadExit);
			} else {
				process_pthread_exit_worker(child, isMain);
			}
		}
	}

	// TODO: what is this function trying to do for pthread_create? What kind of
	// transformation and why?
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
						} else if (arg instanceof IdentifierExpressionNode) {
							IdentifierExpressionNode threadName = (IdentifierExpressionNode) funcCall
									.getArgument(2);

							funcList.add(threadName.getIdentifier().name());
						} else if (arg instanceof CastNode) {
							IdentifierExpressionNode threadName = (IdentifierExpressionNode) ((CastNode) arg)
									.getArgument();

							funcList.add(threadName.getIdentifier().name());
						} else {
							throw new CIVLUnimplementedFeatureException(
									"unimplemented handling of Pthread transformer for expression of "
											+ arg.expressionKind()
											+ " kind as the function pointer argument of pthread_create()");
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

	/**
	 * 
	 * @param type
	 * @return
	 */
	private boolean isVoidPointerType(TypeNode type) {
		if (type.kind() == TypeNodeKind.POINTER) {
			PointerTypeNode pointer = (PointerTypeNode) type;

			if (pointer.referencedType().kind() == TypeNodeKind.VOID)
				return true;
		}
		return false;
	}

	/*
	 * 
	 */

	private boolean hasReturn(ASTNode node) {
		if (node instanceof ReturnNode) {
			return true;
		} else {
			for (ASTNode child : node.children()) {
				if (child != null) {
					if (hasReturn(child)) {
						return true;
					}
				}
			}
		}
		return false;
	}

	/* ********************* Methods From BaseTransformer ****************** */

	@Override
	public AST transform(AST ast) throws SyntaxException {
		SequenceNode<BlockItemNode> root = ast.getRootNode();

		assert this.astFactory == ast.getASTFactory();
		assert this.nodeFactory == astFactory.getNodeFactory();
		ast.release();
		processRoot(root);
		this.completeSources(root);
		AST result = astFactory.newAST(root, ast.getSourceFiles());
		// result.prettyPrint(System.out, false);
		return result;
	}
}
