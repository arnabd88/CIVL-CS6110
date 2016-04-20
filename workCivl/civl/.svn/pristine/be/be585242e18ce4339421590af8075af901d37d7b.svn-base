package edu.udel.cis.vsl.civl.transform.common;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.entity.IF.Entity;
import edu.udel.cis.vsl.abc.ast.entity.IF.Entity.EntityKind;
import edu.udel.cis.vsl.abc.ast.entity.IF.Function;
import edu.udel.cis.vsl.abc.ast.entity.IF.OrdinaryEntity;
import edu.udel.cis.vsl.abc.ast.entity.IF.Variable;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.DeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.CastNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode.ExpressionKind;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ExpressionStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ForLoopInitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.LoopNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.FunctionTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode.TypeNodeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.ast.type.IF.Type.TypeKind;
import edu.udel.cis.vsl.abc.front.IF.CivlcTokenConstant;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.transform.IF.NameTransformer;
import edu.udel.cis.vsl.abc.transform.IF.Transform;
import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.model.IF.CIVLSyntaxException;
import edu.udel.cis.vsl.civl.model.IF.ModelConfiguration;
import edu.udel.cis.vsl.civl.transform.IF.GeneralTransformer;

/**
 * The general transformer performs the following transformations:
 * 
 * <ul>
 * <li>malloc(...) to $malloc($gen_root, ...); where $gen_root is the root scope
 * of this AST (which is reserved as a relative root if other transformers make
 * this AST as part of another)</li>
 * <li>
 * introduce input variables for argc and argv</li>
 * <li>
 * introduce new file scope function $gen_root_function that calls the main
 * function</li>
 * <li>arguments of the main function argc and argv become input variables</li>
 * <li>static variables are all moved to the root scope</li>
 * </ul>
 * 
 * @author Manchun Zheng
 *
 */
public class GeneralWorker extends BaseWorker {

	private final static int DEFAULT_ARGV_SIZE = 10;
	private final static String MALLOC = "malloc";
	final static String GENERAL_ROOT = ModelConfiguration.GENERAL_ROOT;
	private final static String separator = "$";
	// private final static String INPUT_PREFIX = "_gen_";
	private int static_var_count = 0;
	private String CIVL_argc_name;
	private String CIVL_argv_name;
	final static String _argvName = "_gen_argv_tmp";
	private StatementNode argcAssumption = null;
	private Source mainSource;
	private CIVLConfiguration config;
	/**
	 * static variable declaration nodes of this AST
	 */
	private List<VariableDeclarationNode> static_variables = new LinkedList<>();
	private boolean argcUsed = false;
	private boolean argvUsed = false;

	public GeneralWorker(ASTFactory astFactory, CIVLConfiguration config) {
		super(GeneralTransformer.LONG_NAME, astFactory);
		this.identifierPrefix = "_gen_";
		this.config = config;
	}

	@Override
	public AST transform(AST unit) throws SyntaxException {
		SequenceNode<BlockItemNode> root = unit.getRootNode();
		AST newAst;
		List<VariableDeclarationNode> inputVars = new ArrayList<>();
		List<BlockItemNode> newExternalList = new ArrayList<>();
		OrdinaryEntity mainEntity = unit.getInternalOrExternalEntity(MAIN);
		FunctionDefinitionNode newMainFunction = null;
		// VariableDeclarationNode _argv = null;
		Function mainFunction;
		FunctionDefinitionNode mainDef;

		if (mainEntity == null) {
			throw new SyntaxException("missing main function", unit
					.getRootNode().getSource());
		}
		if (!(mainEntity instanceof Function)) {
			throw new SyntaxException("non-function entity with name \"main\"",
					mainEntity.getFirstDeclaration().getSource());
		}
		mainFunction = (Function) mainEntity;
		mainDef = mainFunction.getDefinition();
		checkAgumentsOfMainFunction(mainDef, root);
		unit = renameStaticVariables(unit);
		unit.release();
		root = moveStaticVariables(root);
		processMalloc(root);
		// remove main prototypes...
		for (DeclarationNode decl : mainFunction.getDeclarations()) {
			if (!decl.isDefinition()) {
				decl.parent().removeChild(decl.childIndex());
			}
		}
		this.mainSource = mainDef.getSource();
		inputVars = getInputVariables(mainDef);
		if (inputVars.size() > 0) {
			// the original main has parameters, need to transform main to _main
			// TODO add new argv _argv
			transformMainFunction(root);
			newMainFunction = createNewMainFunction();
		}
		// no need to modify the body of main
		// processArgvRefs(mainDef.getBody());
		for (BlockItemNode inputVar : inputVars)
			newExternalList.add(inputVar);
		if (this.argcAssumption != null) {
			newExternalList.add(this.assumeFunctionDeclaration(argcAssumption
					.getSource()));
			newExternalList.add(argcAssumption);
		}
		// if (_argv != null)
		// newExternalList.add(_argv);
		// add my root
		newExternalList.add(this.generalRootScopeNode());
		for (BlockItemNode child : root) {
			if (child != null) {
				newExternalList.add(child);
				child.parent().removeChild(child.childIndex());
			}
		}
		if (newMainFunction != null)
			newExternalList.add(newMainFunction);
		root = nodeFactory.newSequenceNode(root.getSource(), "TranslationUnit",
				newExternalList);
		this.completeSources(root);
		newAst = astFactory.newAST(root, unit.getSourceFiles(),
				unit.isWholeProgram());
		// newAst.prettyPrint(System.out, true);
		return newAst;
	}

	private void checkAgumentsOfMainFunction(FunctionDefinitionNode main,
			SequenceNode<BlockItemNode> root) {
		FunctionTypeNode functionType = main.getTypeNode();
		SequenceNode<VariableDeclarationNode> parameters = functionType
				.getParameters();

		if (parameters.numChildren() == 2)
			this.checkAgumentsOfMainFunctionWorker(
					parameters.getSequenceChild(0),
					parameters.getSequenceChild(1), main.getBody());
	}

	private void checkAgumentsOfMainFunctionWorker(
			VariableDeclarationNode argc, VariableDeclarationNode argv,
			ASTNode node) {
		if (node instanceof IdentifierExpressionNode) {
			IdentifierNode identifier = ((IdentifierExpressionNode) node)
					.getIdentifier();
			Entity entity = identifier.getEntity();

			if (entity.getEntityKind() == EntityKind.VARIABLE) {
				VariableDeclarationNode variable = ((Variable) entity)
						.getDefinition();

				if (variable != null)
					if (variable.equals(argc))
						this.argcUsed = true;
					else if (variable.equals(argv))
						this.argvUsed = true;
			}
		} else {
			for (ASTNode child : node.children()) {
				if (child == null)
					continue;
				checkAgumentsOfMainFunctionWorker(argc, argv, child);
				if (this.argcUsed && this.argvUsed)
					return;
			}
		}
	}

	private VariableDeclarationNode create_argv() throws SyntaxException {
		TypeNode arrayOfCharPointer = nodeFactory.newArrayTypeNode(this
				.newSource("new main function", CivlcTokenConstant.TYPE),
				nodeFactory.newPointerTypeNode(this.newSource(
						"new main function", CivlcTokenConstant.POINTER), this
						.basicType(BasicTypeKind.CHAR)), this
						.getUpperBoundOfArgvSize());

		return this.variableDeclaration(_argvName, arrayOfCharPointer);
	}

	private ExpressionNode getUpperBoundOfArgvSize() throws SyntaxException {
		Map<String, Object> inputVariables = config.inputVariables();

		if (inputVariables != null
				&& inputVariables.containsKey(CIVL_argc_name)) {
			Object CIVL_argc_obj = inputVariables.get(CIVL_argc_name);

			assert CIVL_argc_obj instanceof BigInteger;
			return this
					.integerConstant(((BigInteger) CIVL_argc_obj).intValue());
		}
		return this.integerConstant(DEFAULT_ARGV_SIZE);
	}

	/**
	 * creates a new main function:
	 * 
	 * <pre>
	 * void main(){
	 *     for(int i=0; i &lt; 10; i = i + 1)
	 *       _argv[i] = &CIVL_argv[i][0];
	 *     _main(CIVL_argc, &_argv[0]);
	 * }
	 * </pre>
	 * 
	 * @return
	 * @throws SyntaxException
	 */
	private FunctionDefinitionNode createNewMainFunction()
			throws SyntaxException {
		LoopNode forLoop;
		ForLoopInitializerNode loopInit;
		ExpressionNode condition, increment;
		StatementNode loopBody;
		ExpressionNode lhs, rhs;
		ExpressionNode addressOf_argv0;
		FunctionCallNode callMain;
		List<BlockItemNode> blockItems = new LinkedList<>();
		FunctionTypeNode mainFuncType;
		VariableDeclarationNode _argv = this.create_argv();

		loopInit = nodeFactory.newForLoopInitializerNode(this.newSource(
				"new main function", CivlcTokenConstant.INIT_DECLARATOR),
				Arrays.asList(this.variableDeclaration("i", this
						.basicType(BasicTypeKind.INT), nodeFactory
						.newIntegerConstantNode(this.newSource(
								"new main function",
								CivlcTokenConstant.INTEGER_CONSTANT), "0"))));
		condition = nodeFactory.newOperatorNode(this.newSource(
				"new main function", CivlcTokenConstant.OPERATOR), Operator.LT,
				Arrays.asList(this.identifierExpression("i"),
						this.getUpperBoundOfArgvSize()));
		increment = nodeFactory.newOperatorNode(this.newSource(
				"new main function", CivlcTokenConstant.OPERATOR),
				Operator.POSTINCREMENT, Arrays.asList(this
						.identifierExpression("i")));
		// _argv[i]
		lhs = nodeFactory.newOperatorNode(this.newSource("new main function",
				CivlcTokenConstant.OPERATOR), Operator.SUBSCRIPT, Arrays
				.asList(this.identifierExpression(_argvName), this
						.identifierExpression(this.newSource(
								"new main function",
								CivlcTokenConstant.IDENTIFIER), "i")));
		// CIVL_argv[i]
		rhs = nodeFactory.newOperatorNode(this.newSource("new main function",
				CivlcTokenConstant.OPERATOR), Operator.SUBSCRIPT, Arrays
				.asList(this.identifierExpression(this.newSource(
						"new main function", CivlcTokenConstant.IDENTIFIER),
						CIVL_argv_name), this.identifierExpression(this
						.newSource("new main function",
								CivlcTokenConstant.INTEGER_CONSTANT), "i")));
		// CIVL_argv[i][0]
		rhs = nodeFactory.newOperatorNode(this.newSource("new main function",
				CivlcTokenConstant.OPERATOR), Operator.SUBSCRIPT, Arrays
				.asList(rhs, nodeFactory.newIntegerConstantNode(this.newSource(
						"new main function",
						CivlcTokenConstant.INTEGER_CONSTANT), "0")));
		// &CIVL_argv[i][0]
		rhs = nodeFactory.newOperatorNode(this.newSource("new main function",
				CivlcTokenConstant.OPERATOR), Operator.ADDRESSOF, Arrays
				.asList(rhs));
		loopBody = nodeFactory.newExpressionStatementNode(nodeFactory
				.newOperatorNode(this.newSource("new main function",
						CivlcTokenConstant.OPERATOR), Operator.ASSIGN, Arrays
						.asList(lhs, rhs)));
		forLoop = nodeFactory.newForLoopNode(
				this.newSource("new main function", CivlcTokenConstant.FOR),
				loopInit, condition, increment, loopBody, null);
		// _argv[0];
		addressOf_argv0 = nodeFactory.newOperatorNode(this.newSource(
				"new main function", CivlcTokenConstant.OPERATOR),
				Operator.SUBSCRIPT, Arrays.asList(this
						.identifierExpression(_argvName), nodeFactory
						.newIntegerConstantNode(this.newSource(
								"new main function",
								CivlcTokenConstant.INTEGER_CONSTANT), "0")));
		// &_argv[0];
		addressOf_argv0 = nodeFactory.newOperatorNode(this.newSource(
				"new main function", CivlcTokenConstant.OPERATOR),
				Operator.ADDRESSOF, Arrays.asList(addressOf_argv0));
		// argv = &_argv[0];
		// assignArgv = nodeFactory.newOperatorNode(
		// this.newSource("new main function", CParser.OPERATOR),
		// Operator.ASSIGN,
		// Arrays.asList(this.identifierExpression(argvName), assignArgv));
		callMain = nodeFactory.newFunctionCallNode(this.newSource(
				"new main function", CivlcTokenConstant.CALL), this
				.identifierExpression(GEN_MAIN), Arrays.asList(
				this.identifierExpression(CIVL_argc_name), addressOf_argv0),
				null);
		blockItems.add(_argv);
		blockItems.add(forLoop);
		blockItems.add(nodeFactory.newExpressionStatementNode(callMain));
		mainFuncType = nodeFactory.newFunctionTypeNode(mainSource, nodeFactory
				.newBasicTypeNode(mainSource, BasicTypeKind.INT), nodeFactory
				.newSequenceNode(this.newSource("new main function",
						CivlcTokenConstant.PARAMETER_TYPE_LIST),
						"formal parameter types",
						new LinkedList<VariableDeclarationNode>()), false);

		return nodeFactory.newFunctionDefinitionNode(this.mainSource,
				this.identifier(MAIN), mainFuncType, null,
				nodeFactory.newCompoundStatementNode(mainSource, blockItems));
	}

	private VariableDeclarationNode generalRootScopeNode() {
		return nodeFactory.newVariableDeclarationNode(mainSource,
				nodeFactory.newIdentifierNode(mainSource, GENERAL_ROOT),
				nodeFactory.newScopeTypeNode(mainSource),
				nodeFactory.newHereNode(mainSource));
	}

	// private void processArgvRefs(ASTNode node) throws SyntaxException {
	// if (node instanceof OperatorNode
	// && ((OperatorNode) node).getOperator() == Operator.SUBSCRIPT) {
	// ASTNode parent = node.parent();
	//
	// if (!(parent instanceof OperatorNode && (((OperatorNode) parent)
	// .getOperator() == Operator.ADDRESSOF))
	// && !(parent instanceof CastNode)) {
	// OperatorNode subscript = (OperatorNode) node;
	// ExpressionNode arg0 = subscript.getArgument(0);
	//
	// if (arg0.expressionKind() == ExpressionKind.IDENTIFIER_EXPRESSION) {
	// IdentifierExpressionNode idExpr = (IdentifierExpressionNode) arg0;
	//
	// if (idExpr.getIdentifier().name().equals(this.argvName)) {
	// OperatorNode newSubscript = subscript.copy();
	// IdentifierExpressionNode newIdExpr = idExpr.copy();
	// Source source = subscript.getSource();
	// ExpressionNode addreessOf;
	//
	// newIdExpr.getIdentifier().setName(CIVL_argv_name);
	// newSubscript.setChild(0, newIdExpr);
	// newSubscript = nodeFactory.newOperatorNode(source,
	// Operator.SUBSCRIPT, Arrays.asList(newSubscript,
	// nodeFactory.newIntegerConstantNode(
	// source, "0")));
	// addreessOf = nodeFactory.newOperatorNode(source,
	// Operator.ADDRESSOF,
	// Arrays.asList((ExpressionNode) newSubscript));
	// node.parent().setChild(node.childIndex(), addreessOf);
	// }
	// }
	// }
	// } else {
	// for (ASTNode child : node.children())
	// if (child != null)
	// processArgvRefs(child);
	// }
	// }

	private void processMalloc(ASTNode node) {
		if (node instanceof FunctionCallNode) {
			FunctionCallNode funcCall = (FunctionCallNode) node;

			if (funcCall.getFunction().expressionKind() == ExpressionKind.IDENTIFIER_EXPRESSION) {
				IdentifierExpressionNode functionExpression = (IdentifierExpressionNode) funcCall
						.getFunction();
				String functionName = functionExpression.getIdentifier().name();

				if (functionName.equals(MALLOC)) {
					ASTNode parent = funcCall.parent();
					ExpressionNode myRootScope = this.identifierExpression(
							funcCall.getSource(), GENERAL_ROOT);
					int callIndex = funcCall.childIndex();
					ExpressionNode argument = funcCall.getArgument(0);

					functionExpression.getIdentifier().setName("$" + MALLOC);
					argument.parent().removeChild(argument.childIndex());
					funcCall.setArguments(nodeFactory.newSequenceNode(
							argument.getSource(), "Actual Parameters",
							Arrays.asList(myRootScope, argument)));
					if (!(parent instanceof CastNode)) {
						funcCall.remove();
						if (parent instanceof OperatorNode) {
							ExpressionNode lhs = ((OperatorNode) parent)
									.getArgument(0);
							Type type = lhs.getInitialType();
							TypeNode typeNode;
							CastNode castNode;

							if (type.kind() != TypeKind.POINTER)
								throw new CIVLSyntaxException(
										"The left hand side of a malloc call must be of pointer"
												+ " type.", lhs.getSource());
							typeNode = this.typeNode(lhs.getSource(), type);
							castNode = nodeFactory.newCastNode(
									funcCall.getSource(), typeNode, funcCall);
							parent.setChild(callIndex, castNode);
						} else if (parent instanceof VariableDeclarationNode) {
							VariableDeclarationNode variable = (VariableDeclarationNode) parent;
							CastNode castNode = nodeFactory.newCastNode(
									funcCall.getSource(), variable
											.getTypeNode().copy(), funcCall);

							variable.setInitializer(castNode);
						}
					}
				}
			}
		} else {
			for (ASTNode child : node.children()) {
				if (child != null)
					processMalloc(child);
			}
		}

	}

	/**
	 * Processes the original main function, including:
	 * <ul>
	 * <li>Removes all arguments of the function;</li>
	 * </ul>
	 * 
	 * @param mainFunction
	 *            The function definition node representing the original main
	 *            function.
	 * @param vars
	 *            The list of variable declaration nodes that are the arguments
	 *            of the original main function. These variables will be moved
	 *            up to the higher scope (i.e., the file scope of the final AST)
	 *            and become $input variables of the final AST. When invoking
	 *            this function, this parameter should be an empty list and this
	 *            function will update this list.
	 * @throws SyntaxException
	 */
	private List<VariableDeclarationNode> getInputVariables(
			FunctionDefinitionNode mainFunction) throws SyntaxException {
		List<VariableDeclarationNode> inputVars = new ArrayList<>();
		FunctionTypeNode functionType = mainFunction.getTypeNode();
		SequenceNode<VariableDeclarationNode> parameters = functionType
				.getParameters();
		int count = parameters.numChildren();

		if (count != 0 && count != 2) {
			if (count == 1) {
				if (parameters.getSequenceChild(0).getTypeNode().typeNodeKind() != TypeNodeKind.VOID)
					throw new SyntaxException(
							"The main function should have 0 or 2 parameters instead of "
									+ count, mainFunction.getSource());
			} else
				throw new SyntaxException(
						"The main function should have 0 or 2 parameters instead of "
								+ count, mainFunction.getSource());
		}
		if (count == 2 && (this.argvUsed || this.argcUsed)) {
			VariableDeclarationNode argc = parameters.getSequenceChild(0);
			VariableDeclarationNode argv = parameters.getSequenceChild(1);
			VariableDeclarationNode CIVL_argc = argc.copy();
			VariableDeclarationNode CIVL_argv;
			String argcName = argc.getIdentifier().name();
			String argvName = argv.getIdentifier().name();

			this.CIVL_argc_name = identifierPrefix + argcName;
			this.CIVL_argv_name = identifierPrefix + argvName;
			CIVL_argc.getTypeNode().setInputQualified(true);
			CIVL_argc.getIdentifier().setName(this.CIVL_argc_name);
			inputVars.add(CIVL_argc);
			CIVL_argv = inputArgvDeclaration(argv, CIVL_argv_name);
			inputVars.add(CIVL_argv);
			if (config.inputVariables() == null
					|| !config.inputVariables().containsKey(CIVL_argc_name))
				this.argcAssumption = this.argcAssumption(argc.getSource(),
						this.CIVL_argc_name);
		} else if (count == 2) {
			functionType.setParameters(this.nodeFactory.newSequenceNode(
					parameters.getSource(), "Formal Parameter List",
					new ArrayList<VariableDeclarationNode>(0)));
		}
		return inputVars;
	}

	/**
	 * $assume 0 < argc && argc < MAX_ARGC;
	 * 
	 * @param source
	 * @param argcName
	 * @return
	 * @throws SyntaxException
	 */
	private ExpressionStatementNode argcAssumption(Source source,
			String argcName) throws SyntaxException {
		ExpressionNode lowerBound = nodeFactory.newOperatorNode(source,
				Operator.LT, Arrays.asList(
						nodeFactory.newIntegerConstantNode(source, "0"),
						this.identifierExpression(source, argcName)));
		ExpressionNode upperBound = nodeFactory.newOperatorNode(
				source,
				Operator.LT,
				Arrays.asList(this.identifierExpression(source, argcName),
						this.integerConstant(DEFAULT_ARGV_SIZE)));

		return nodeFactory.newExpressionStatementNode(this.functionCall(source,
				ASSUME, Arrays.asList((ExpressionNode) nodeFactory
						.newOperatorNode(source, Operator.LAND,
								Arrays.asList(lowerBound, upperBound)))));
	}

	/**
	 * Declares <code>$input char CIVL_argv[MAX_ARGC][];</code>.
	 * 
	 * @param oldArgv
	 * @return
	 * @throws SyntaxException
	 */
	private VariableDeclarationNode inputArgvDeclaration(
			VariableDeclarationNode oldArgv, String argvNewName)
			throws SyntaxException {
		VariableDeclarationNode __argv = oldArgv.copy();
		Source source = oldArgv.getSource();
		TypeNode arrayOfString = nodeFactory.newArrayTypeNode(
				source,
				nodeFactory.newArrayTypeNode(oldArgv.getSource(),
						this.basicType(BasicTypeKind.CHAR), null),
				this.getUpperBoundOfArgvSize());

		__argv.getIdentifier().setName(argvNewName);
		arrayOfString.setInputQualified(true);
		__argv.setTypeNode(arrayOfString);
		return __argv;
	}

	public enum ArgvTypeKind {
		POINTER_POINTER_CHAR, ARRAY_POINTER_CHAR, ARRAY_ARRAY_CAHR
	};

	// private ArgvTypeKind analyzeArgvType(TypeNode type) throws
	// SyntaxException {
	// TypeNodeKind typeKind = type.typeNodeKind();
	//
	// switch (typeKind) {
	// case POINTER:
	// return ArgvTypeKind.POINTER_POINTER_CHAR;
	// case ARRAY:
	// ArrayTypeNode arrayType = (ArrayTypeNode) type;
	// TypeNode arrayEleType = arrayType.getElementType();
	// TypeKind arrayEleTypeKind = arrayEleType.getType().kind();
	//
	// if (arrayEleTypeKind == TypeKind.POINTER)
	// return ArgvTypeKind.ARRAY_POINTER_CHAR;
	// else if (arrayEleTypeKind == TypeKind.ARRAY)
	// return ArgvTypeKind.ARRAY_ARRAY_CAHR;
	// default:
	// throw new SyntaxException("Invalid type " + type.getType()
	// + " for argv of main.", null);
	// }
	// }

	private AST renameStaticVariables(AST ast) throws SyntaxException {
		Map<Entity, String> newNameMap = new HashMap<>();
		NameTransformer staticVariableNameTransformer;

		newNameMap = newNameMapOfStaticVariables(ast.getRootNode(),
				ast.getRootNode(), newNameMap);
		staticVariableNameTransformer = Transform.nameTransformer(newNameMap,
				astFactory);
		return staticVariableNameTransformer.transform(ast);
	}

	// TODO can you have static for function parameters?
	// TODO what if the initializer of the variable node access some variables
	// not declared in the root scope?
	// TODO what if the type is defined somewhere in the AST?
	/**
	 * Computes the new name map of static variables. A static variable "var" is
	 * renamed to "var$n", where n is the current static variable ID.
	 * 
	 * @param node
	 * @param newNames
	 * @return
	 */
	private Map<Entity, String> newNameMapOfStaticVariables(ASTNode root,
			ASTNode node, Map<Entity, String> newNames) {
		if (node instanceof VariableDeclarationNode) {
			VariableDeclarationNode variable = (VariableDeclarationNode) node;

			if (variable.hasStaticStorage()) {
				String oldName = variable.getName();
				String newName = oldName + separator + this.static_var_count++;

				newNames.put(variable.getEntity(), newName);
				// don't move the variable if it is already in the root scope
				if (!variable.parent().equals(root))
					this.static_variables.add(variable);
			}
		} else {
			for (ASTNode child : node.children()) {
				if (child == null)
					continue;
				newNames = newNameMapOfStaticVariables(root, child, newNames);
			}
		}
		return newNames;
	}

	private SequenceNode<BlockItemNode> moveStaticVariables(
			SequenceNode<BlockItemNode> root) {
		if (this.static_variables.size() < 1)
			return root;

		List<BlockItemNode> newChildren = new LinkedList<>();
		int count = root.numChildren();

		for (VariableDeclarationNode var : this.static_variables) {
			var.remove();
			newChildren.add(var);
		}
		for (int i = 0; i < count; i++) {
			BlockItemNode child = root.getSequenceChild(i);

			if (child == null)
				continue;
			child.remove();
			newChildren.add(child);
		}
		return nodeFactory
				.newTranslationUnitNode(root.getSource(), newChildren);
	}
}
