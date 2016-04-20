package edu.udel.cis.vsl.civl.transform.common;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode.NodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.ExternalDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.CastNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode.ExpressionKind;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.AssumeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CompoundStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ForLoopInitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.LoopNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.FunctionTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode.TypeNodeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.ast.type.IF.Type.TypeKind;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSyntaxException;

public class GeneralTransformer extends CIVLBaseTransformer {

	public final static String CODE = "general";
	public final static String LONG_NAME = "GeneralTransformer";
	public final static String SHORT_DESCRIPTION = "transforms general features of C programs to CIVL-C";

	private final static String MALLOC = "malloc";
	private final static String MY_ROOT_SCOPE = "CIVL_root";
	private final static String MAX_ARGC = "10";

	private final static String INPUT_PREFIX = "CIVL_";

	private String argvName;
	private String newArgvName;
	private AssumeNode argcAssumption = null;
	private Source mainSource;

	public GeneralTransformer(ASTFactory astFactory) {
		super(CODE, LONG_NAME, SHORT_DESCRIPTION, astFactory);
	}

	@Override
	public AST transform(AST unit) throws SyntaxException {
		SequenceNode<ExternalDefinitionNode> root = unit.getRootNode();
		AST newAst;
		List<VariableDeclarationNode> inputVars = new ArrayList<>();
		List<ExternalDefinitionNode> newExternalList = new ArrayList<>();
		Map<String, VariableDeclarationNode> macroVars = new HashMap<>();

		unit.release();
		processMalloc(root);
		for (ASTNode child : root) {
			if (child.nodeKind() == NodeKind.FUNCTION_DEFINITION) {
				FunctionDefinitionNode functionNode = (FunctionDefinitionNode) child;
				IdentifierNode functionName = (IdentifierNode) functionNode
						.child(0);

				if (functionName.name().equals("main")) {
					this.mainSource = functionNode.getSource();
					inputVars = processMainFunction(functionNode);
					processArgvRefs(functionNode.getBody());
				}
			}
			// TODO factor this out
			// if (config.svcomp())
			// recoverMacro(child, macroVars);
		}
		for (ExternalDefinitionNode inputVar : macroVars.values())
			newExternalList.add(inputVar);
		for (ExternalDefinitionNode inputVar : inputVars)
			newExternalList.add(inputVar);
		if (this.argcAssumption != null)
			newExternalList.add(argcAssumption);
		// add my root
		newExternalList.add(this.myRootNode());
		for (ExternalDefinitionNode child : root) {
			newExternalList.add(child);
			child.parent().removeChild(child.childIndex());
		}
		root = nodeFactory.newSequenceNode(root.getSource(), "TranslationUnit",
				newExternalList);
		newAst = astFactory.newAST(root);
		return newAst;
	}

	private VariableDeclarationNode myRootNode() {
		return nodeFactory.newVariableDeclarationNode(mainSource,
				nodeFactory.newIdentifierNode(mainSource, MY_ROOT_SCOPE),
				nodeFactory.newScopeTypeNode(mainSource),
				nodeFactory.newHereNode(mainSource));
	}

	private void processArgvRefs(ASTNode node) throws SyntaxException {
		if (node instanceof OperatorNode
				&& ((OperatorNode) node).getOperator() == Operator.SUBSCRIPT) {
			ASTNode parent = node.parent();

			if (!(parent instanceof OperatorNode && (((OperatorNode) parent)
					.getOperator() == Operator.ADDRESSOF))
					&& !(parent instanceof CastNode)) {
				OperatorNode subscript = (OperatorNode) node;
				ExpressionNode arg0 = subscript.getArgument(0);

				if (arg0.expressionKind() == ExpressionKind.IDENTIFIER_EXPRESSION) {
					IdentifierExpressionNode idExpr = (IdentifierExpressionNode) arg0;

					if (idExpr.getIdentifier().name().equals(this.argvName)) {
						OperatorNode newSubscript = subscript.copy();
						IdentifierExpressionNode newIdExpr = idExpr.copy();
						Source source = subscript.getSource();
						ExpressionNode addreessOf;

						newIdExpr.getIdentifier().setName(newArgvName);
						newSubscript.setChild(0, newIdExpr);
						newSubscript = nodeFactory.newOperatorNode(source,
								Operator.SUBSCRIPT, Arrays.asList(newSubscript,
										nodeFactory.newIntegerConstantNode(
												source, "0")));
						addreessOf = nodeFactory.newOperatorNode(source,
								Operator.ADDRESSOF,
								Arrays.asList((ExpressionNode) newSubscript));
						node.parent().setChild(node.childIndex(), addreessOf);
					}
				}
			}
		} else {
			for (ASTNode child : node.children())
				if (child != null)
					processArgvRefs(child);
		}
	}

	private void processMalloc(ASTNode node) {
		if (node instanceof FunctionCallNode) {
			FunctionCallNode funcCall = (FunctionCallNode) node;

			if (funcCall.getFunction().expressionKind() == ExpressionKind.IDENTIFIER_EXPRESSION) {
				IdentifierExpressionNode functionExpression = (IdentifierExpressionNode) funcCall
						.getFunction();
				String functionName = functionExpression.getIdentifier().name();

				if (functionName.equals(MALLOC)) {
					ASTNode parent = funcCall.parent();
					int callIndex = funcCall.childIndex();
					ExpressionNode myRootScope = this.identifierExpression(
							funcCall.getSource(), MY_ROOT_SCOPE);
					ExpressionNode argument = funcCall.getArgument(0);

					functionExpression.getIdentifier().setName("$" + MALLOC);
					argument.parent().removeChild(argument.childIndex());
					funcCall.setArguments(nodeFactory.newSequenceNode(
							argument.getSource(), "Actual Parameters",
							Arrays.asList(myRootScope, argument)));
					if (!(parent instanceof CastNode)) {
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
							parent.removeChild(callIndex);
							castNode = nodeFactory.newCastNode(
									funcCall.getSource(), typeNode, funcCall);
							parent.setChild(callIndex, castNode);
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
	private List<VariableDeclarationNode> processMainFunction(
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
		if (count == 2) {
			VariableDeclarationNode argc = parameters.getSequenceChild(0);
			VariableDeclarationNode argv = parameters.getSequenceChild(1);
			VariableDeclarationNode CIVL_argc = argc.copy();
			VariableDeclarationNode CIVL_argv, _argv;
			String argcName = argc.getIdentifier().name();
			String argvName = argv.getIdentifier().name();
			String _argvName = "_" + argvName;
			String newArgcName = INPUT_PREFIX + argcName;
			Source source = argv.getTypeNode().getSource();
			TypeNode pointerOfPointerOfChar = nodeFactory.newPointerTypeNode(
					source, nodeFactory.newPointerTypeNode(source, nodeFactory
							.newBasicTypeNode(source, BasicTypeKind.CHAR)));
			CompoundStatementNode functionBody = mainFunction.getBody();
			TypeNode arrayOfCharPointer = nodeFactory.newArrayTypeNode(source,
					nodeFactory.newPointerTypeNode(source, nodeFactory
							.newBasicTypeNode(source, BasicTypeKind.CHAR)),
					nodeFactory.newIntegerConstantNode(source, MAX_ARGC));
			LoopNode forLoop;
			ForLoopInitializerNode loopInit;
			ExpressionNode condition, increment;
			StatementNode loopBody;
			ExpressionNode lhs, rhs;
			ExpressionNode assignArgv;

			this.argvName = argvName;
			this.newArgvName = INPUT_PREFIX + argvName;
			parameters.removeChild(0);
			parameters.removeChild(1);
			CIVL_argc.getTypeNode().setInputQualified(true);
			CIVL_argc.getIdentifier().setName(newArgcName);
			inputVars.add(CIVL_argc);
			CIVL_argv = inputArgvDeclaration(argv, newArgvName);
			inputVars.add(CIVL_argv);
			functionType.setParameters(nodeFactory.newSequenceNode(
					parameters.getSource(), "FormalParameterDeclarations",
					new ArrayList<VariableDeclarationNode>(0)));
			this.argcAssumption = this.argcAssumption(argc.getSource(),
					newArgcName);
			argc.setInitializer(this.identifierExpression(argc.getSource(),
					newArgcName));
			argv.setTypeNode(pointerOfPointerOfChar);
			_argv = argv.copy();
			_argv.getIdentifier().setName(_argvName);
			_argv.setTypeNode(arrayOfCharPointer);
			source = argv.getSource();
			loopInit = nodeFactory.newForLoopInitializerNode(source, Arrays
					.asList(this.variableDeclaration(source, "i", nodeFactory
							.newBasicTypeNode(source, BasicTypeKind.INT),
							nodeFactory.newIntegerConstantNode(source, "0"))));
			condition = nodeFactory.newOperatorNode(source, Operator.LT, Arrays
					.asList(this.identifierExpression(source, "i"), nodeFactory
							.newIntegerConstantNode(source, MAX_ARGC)));
			increment = nodeFactory.newOperatorNode(source,
					Operator.POSTINCREMENT,
					Arrays.asList(this.identifierExpression(source, "i")));
			// _argv[i]
			lhs = nodeFactory.newOperatorNode(source, Operator.SUBSCRIPT,
					Arrays.asList(this.identifierExpression(source, _argvName),
							this.identifierExpression(source, "i")));
			// CIVL_argv[i]
			rhs = nodeFactory.newOperatorNode(source, Operator.SUBSCRIPT,
					Arrays.asList(
							this.identifierExpression(source, newArgvName),
							this.identifierExpression(source, "i")));
			// CIVL_argv[i][0]
			rhs = nodeFactory.newOperatorNode(
					source,
					Operator.SUBSCRIPT,
					Arrays.asList(rhs,
							nodeFactory.newIntegerConstantNode(source, "0")));
			// &CIVL_argv[i][0]
			rhs = nodeFactory.newOperatorNode(source, Operator.ADDRESSOF,
					Arrays.asList(rhs));
			loopBody = nodeFactory.newExpressionStatementNode(nodeFactory
					.newOperatorNode(source, Operator.ASSIGN,
							Arrays.asList(lhs, rhs)));
			forLoop = nodeFactory.newForLoopNode(source, loopInit, condition,
					increment, loopBody, null);
			// _argv[0];
			assignArgv = nodeFactory.newOperatorNode(source,
					Operator.SUBSCRIPT, Arrays.asList(
							this.identifierExpression(source, _argvName),
							nodeFactory.newIntegerConstantNode(source, "0")));
			// &_argv[0];
			assignArgv = nodeFactory.newOperatorNode(source,
					Operator.ADDRESSOF, Arrays.asList(assignArgv));
			// argv = &_argv[0];
			assignArgv = nodeFactory.newOperatorNode(source, Operator.ASSIGN,
					Arrays.asList(this.identifierExpression(source, argvName),
							assignArgv));
			functionBody = this.addNodeToBeginning(functionBody,
					nodeFactory.newExpressionStatementNode(assignArgv));
			functionBody = this.addNodeToBeginning(functionBody, forLoop);
			functionBody = this.addNodeToBeginning(functionBody, argv);
			functionBody = this.addNodeToBeginning(functionBody, _argv);
			functionBody = this.addNodeToBeginning(functionBody, argc);
			mainFunction.setBody(functionBody);
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
	private AssumeNode argcAssumption(Source source, String argcName)
			throws SyntaxException {
		ExpressionNode lowerBound = nodeFactory.newOperatorNode(source,
				Operator.LT, Arrays.asList(
						nodeFactory.newIntegerConstantNode(source, "0"),
						this.identifierExpression(source, argcName)));
		ExpressionNode upperBound = nodeFactory.newOperatorNode(source,
				Operator.LT, Arrays.asList(
						this.identifierExpression(source, argcName),
						nodeFactory.newIntegerConstantNode(source, MAX_ARGC)));

		return nodeFactory.newAssumeNode(
				source,
				nodeFactory.newOperatorNode(source, Operator.LAND,
						Arrays.asList(lowerBound, upperBound)));
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
		TypeNode arrayOfString = nodeFactory.newArrayTypeNode(source,
				nodeFactory.newArrayTypeNode(oldArgv.getSource(), nodeFactory
						.newBasicTypeNode(source, BasicTypeKind.CHAR), null),
				nodeFactory.newIntegerConstantNode(source, MAX_ARGC));

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

	private CompoundStatementNode addNodeToBeginning(
			CompoundStatementNode compoundNode, BlockItemNode node) {
		int numChildren = compoundNode.numChildren();
		List<BlockItemNode> nodeList = new ArrayList<>(numChildren + 1);

		nodeList.add(node);
		for (int i = 0; i < numChildren; i++) {
			BlockItemNode child = compoundNode.getSequenceChild(i);

			nodeList.add(child);
			compoundNode.removeChild(i);
		}
		return nodeFactory.newCompoundStatementNode(compoundNode.getSource(),
				nodeList);
	}

}
