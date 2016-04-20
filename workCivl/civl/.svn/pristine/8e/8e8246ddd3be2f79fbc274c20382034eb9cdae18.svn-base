package edu.udel.cis.vsl.civl.model.common;

import java.io.File;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.udel.cis.vsl.abc.ast.conversion.IF.Conversion;
import edu.udel.cis.vsl.abc.ast.conversion.IF.Conversion.ConversionKind;
import edu.udel.cis.vsl.abc.ast.entity.IF.Entity;
import edu.udel.cis.vsl.abc.ast.entity.IF.Entity.EntityKind;
import edu.udel.cis.vsl.abc.ast.entity.IF.Function;
import edu.udel.cis.vsl.abc.ast.entity.IF.Label;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.PairNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.compound.CompoundInitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.compound.CompoundLiteralObject;
import edu.udel.cis.vsl.abc.ast.node.IF.compound.LiteralObject;
import edu.udel.cis.vsl.abc.ast.node.IF.compound.ScalarLiteralObject;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.AbstractFunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.ContractNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.InitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.TypedefDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ArrowNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.CastNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.CompoundLiteralNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ConstantNode.ConstantKind;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.DerivativeExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.DotNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.EnumerationConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode.ExpressionKind;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.HereOrRootNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IntegerConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.QuantifiedExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.RegularRangeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.RemoteExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ResultNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ScopeOfNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.SizeableNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.SizeofNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.SpawnNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.StringLiteralNode;
import edu.udel.cis.vsl.abc.ast.node.IF.label.LabelNode;
import edu.udel.cis.vsl.abc.ast.node.IF.label.OrdinaryLabelNode;
import edu.udel.cis.vsl.abc.ast.node.IF.label.SwitchLabelNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.AtomicNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ChooseStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CivlForNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CompoundStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.DeclarationListNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ExpressionStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ForLoopInitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ForLoopNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.GotoNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.IfNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.JumpNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.JumpNode.JumpKind;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.LabeledStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.LoopNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.NullStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ReturnNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode.StatementKind;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.SwitchNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.WhenNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.EnumerationTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.FunctionTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.StructureOrUnionTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode.TypeNodeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.ArrayType;
import edu.udel.cis.vsl.abc.ast.type.IF.DomainType;
import edu.udel.cis.vsl.abc.ast.type.IF.EnumerationType;
import edu.udel.cis.vsl.abc.ast.type.IF.Enumerator;
import edu.udel.cis.vsl.abc.ast.type.IF.Field;
import edu.udel.cis.vsl.abc.ast.type.IF.FunctionType;
import edu.udel.cis.vsl.abc.ast.type.IF.ObjectType;
import edu.udel.cis.vsl.abc.ast.type.IF.PointerType;
import edu.udel.cis.vsl.abc.ast.type.IF.QualifiedObjectType;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.StructureOrUnionType;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.ast.type.IF.Type.TypeKind;
import edu.udel.cis.vsl.abc.ast.value.IF.CharacterValue;
import edu.udel.cis.vsl.abc.ast.value.IF.IntegerValue;
import edu.udel.cis.vsl.abc.ast.value.IF.RealFloatingValue;
import edu.udel.cis.vsl.abc.ast.value.IF.Value;
import edu.udel.cis.vsl.abc.token.IF.CivlcToken;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.StringLiteral;
import edu.udel.cis.vsl.civl.model.IF.AbstractFunction;
import edu.udel.cis.vsl.civl.model.IF.AccuracyAssumptionBuilder;
import edu.udel.cis.vsl.civl.model.IF.CIVLException;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLSyntaxException;
import edu.udel.cis.vsl.civl.model.IF.CIVLTypeFactory;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.Fragment;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.ModelConfiguration;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ArrayLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression.BINARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ContractClauseExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.FunctionIdentifierExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.IntegerLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.LiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.QuantifiedExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.QuantifiedExpression.Quantifier;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression.UNARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.location.Location.AtomicKind;
import edu.udel.cis.vsl.civl.model.IF.statement.AssignStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.CivlParForSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.MallocStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.NoopStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ReturnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLCompleteDomainType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPointerType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPrimitiveType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPrimitiveType.PrimitiveTypeKind;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLStructOrUnionType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.type.StructOrUnionField;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.model.common.expression.CommonUndefinedProcessExpression;
import edu.udel.cis.vsl.civl.model.common.statement.CommonAtomBranchStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonAtomicLockAssignStatement;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.civl.util.IF.Triple;
import edu.udel.cis.vsl.gmc.CommandLineException;

/**
 * This class translates an AST node of a function body and completes the
 * resulting function accordingly. The only incomplete translation is the call
 * or spawn statements involved in this function, which dont have the
 * corresponding function of invocation set appropriately.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class FunctionTranslator {
	/**
	 * The string type name of the Result Expression:<br>
	 * An special expression used to represent the result of a function in
	 * function contracts.
	 */
	public static final String contractResultName = "$result";

	private static final String PAR_FUNC_NAME = "_par_proc";

	/* ************************** Instance Fields ************************** */

	private int atomicCount = 0;

	private int atomCount = 0;

	/**
	 * Counter for the variable of a counter for $for loop on literal domains.
	 */
	private int literalDomForCounterCount = 0;

	/**
	 * Store temporary information of the function being processed
	 */
	private FunctionInfo functionInfo;

	/**
	 * The unique model factory to be used in the system.
	 */
	private ModelFactory modelFactory;

	/**
	 * The unique type factory to be used in the system.
	 */
	private CIVLTypeFactory typeFactory;

	/**
	 * The unique model builder of the system.
	 */
	private ModelBuilderWorker modelBuilder;

	/**
	 * The AST node of the function body, which is to be used for translation.
	 */
	private StatementNode functionBodyNode;

	/**
	 * The CIVL function that is the result of this function translator.
	 */
	private CIVLFunction function;

	/**
	 * The accuracy assumption builder, which performs Taylor expansions after
	 * assumptions involving abstract functions.
	 */
	@SuppressWarnings("unused")
	private AccuracyAssumptionBuilder accuracyAssumptionBuilder;

	/* **************************** Constructors *************************** */

	/**
	 * Constructs new instance of function translator. This constructor will be
	 * used for translating all function nodes except for the system function.
	 * See also
	 * {@link #FunctionTranslator(ModelBuilderWorker, ModelFactory, CIVLFunction)}
	 * .
	 * 
	 * @param modelBuilder
	 *            The model builder worker where this function translator is
	 *            created.
	 * @param modelFactory
	 *            The unique model factory used by the system to create new
	 *            instances of CIVL expressions, statements, etc.
	 * @param bodyNode
	 *            The AST node of the function body that this function
	 *            translator is going to translate.
	 * @param function
	 *            The CIVL function that will be the result of this function
	 *            translator.
	 */
	FunctionTranslator(ModelBuilderWorker modelBuilder,
			ModelFactory modelFactory, StatementNode bodyNode,
			CIVLFunction function) {
		this.modelBuilder = modelBuilder;
		this.modelFactory = modelFactory;
		this.typeFactory = modelFactory.typeFactory();
		this.functionBodyNode = bodyNode;
		this.setFunction(function);
		this.functionInfo = new FunctionInfo(function);
		this.accuracyAssumptionBuilder = new CommonAccuracyAssumptionBuilder(
				modelFactory);
	}

	/**
	 * Constructs new instance of function translator. This constructor will be
	 * used only for translating the system function, because initially the
	 * model builder worker doesn't know about the function body node of the
	 * system function (i.e., the body node of the main function). It will have
	 * to translate the root nodes before processing the main function. See also
	 * {@link #translateRootFunction(Scope, ASTNode)}.
	 * 
	 * @param modelBuilder
	 *            The model builder worker where this function translator is
	 *            created.
	 * @param modelFactory
	 *            The unique model factory used by the system to create new
	 *            instances of CIVL expressions, statements, etc.
	 * @param bodyNode
	 *            The AST node of the function body that this function
	 *            translator is going to translate.
	 * @param function
	 *            The CIVL function that will be the result of this function
	 *            translator.
	 */
	FunctionTranslator(ModelBuilderWorker modelBuilder,
			ModelFactory modelFactory, CIVLFunction function) {
		this.modelBuilder = modelBuilder;
		this.modelFactory = modelFactory;
		this.typeFactory = modelFactory.typeFactory();
		this.setFunction(function);
		this.functionInfo = new FunctionInfo(function);
		this.accuracyAssumptionBuilder = new CommonAccuracyAssumptionBuilder(
				modelFactory);
	}

	/* *************************** Public Methods ************************** */

	/**
	 * Processes the function body of a function definition node. At least one
	 * function declaration for this function should have been processed
	 * already, so the corresponding CIVL function should already exist.
	 */
	public void translateFunction() {
		Fragment body = this.translateFunctionBody();

		functionInfo.completeFunction(body);
	}

	/**
	 * This method translates the "_CIVL_System" function. The result should be
	 * a function with the following:
	 * <ul>
	 * <li>statements in the global scope, and</li>
	 * <li>statements in the main function body.</li>
	 * </ul>
	 * Initially, the model builder worker have no information about the main
	 * function node. Thus the translation starts at translating the rootNode,
	 * obtaining a list of initialization statements declared in the root scope
	 * and the AST node of the main function.
	 * 
	 * @param systemScope
	 *            The root scope of the model.
	 * @param rootNode
	 *            The root node of the AST for translation.
	 * @throws CIVLSyntaxException
	 *             if no main function node could be found in the rootNode's
	 *             children.
	 */
	public void translateRootFunction(Scope systemScope, ASTNode rootNode) {
		Fragment initialization = new CommonFragment();
		Fragment body;

		modelFactory.addConditionalExpressionQueue();
		for (int i = 0; i < rootNode.numChildren(); i++) {
			ASTNode node = rootNode.child(i);
			Fragment fragment;

			if (node != null) {
				fragment = translateASTNode(node, systemScope, null);
				if (fragment != null)
					initialization = initialization.combineWith(fragment);
			}
		}
		modelFactory.popConditionaExpressionStack();
		if (modelBuilder.mainFunctionNode == null) {
			throw new CIVLSyntaxException("program must have a main function,",
					modelFactory.sourceOf(rootNode));
		} else {
			Function mainFunction = modelBuilder.mainFunctionNode.getEntity();
			FunctionType functionType = mainFunction.getType();
			FunctionTypeNode functionTypeNode = modelBuilder.mainFunctionNode
					.getTypeNode();
			SequenceNode<VariableDeclarationNode> abcParameters = functionTypeNode
					.getParameters();
			int numParameters = abcParameters.numChildren();
			ObjectType abcReturnType = functionType.getReturnType();
			Scope scope = this.function.outerScope();

			if (abcReturnType.kind() != TypeKind.VOID) {
				CIVLType returnType = translateABCType(
						modelFactory.sourceOf(functionTypeNode.getReturnType()
								.getSource()), scope, abcReturnType);

				this.function.setReturnType(returnType);
			}
			if (numParameters > 0) {
				List<Variable> parameters = new ArrayList<>();
				List<CIVLType> parameterTypes = new ArrayList<>();

				for (int i = 0; i < numParameters; i++) {
					VariableDeclarationNode decl = abcParameters
							.getSequenceChild(i);

					if (decl.getTypeNode().kind() == TypeNodeKind.VOID)
						continue;
					else {
						CIVLType type = translateABCType(
								modelFactory.sourceOf(decl), scope,
								functionType.getParameterType(i));
						CIVLSource source = modelFactory.sourceOf(decl
								.getIdentifier());
						Identifier variableName = modelFactory.identifier(
								source, decl.getName());

						parameters.add(modelFactory.variable(source, type,
								variableName, parameters.size()));
						parameterTypes.add(type);
					}
				}
				this.function.setParameters(parameters);
				this.function.setParameterTypes(parameterTypes
						.toArray(new CIVLType[parameterTypes.size()]));
			}
			this.functionBodyNode = modelBuilder.mainFunctionNode.getBody();
			body = this.translateFunctionBody();
			body = initialization.combineWith(body);
			functionInfo.completeFunction(body);
		}
	}

	/* *************************** Private Methods ************************* */

	/**
	 * Translate the function body node associated with this function
	 * translator.
	 * 
	 * @return The fragment of CIVL locations and statements that represents the
	 *         function body node.
	 */
	private Fragment translateFunctionBody() {
		Fragment body;
		Scope scope = this.function.outerScope();

		body = translateStatementNode(scope, this.functionBodyNode);
		if (!containsReturn(body)) {
			CIVLSource endSource = modelFactory
					.sourceOfEnd(this.functionBodyNode);
			Location returnLocation = modelFactory.location(endSource,
					function.outerScope());
			Fragment returnFragment = modelFactory.returnFragment(endSource,
					returnLocation, null, this.functionInfo.function());

			if (body != null)
				body = body.combineWith(returnFragment);
			else
				body = returnFragment;
		}
		return body;
	}

	/* *********************************************************************
	 * Translate ABC Statement Nodes into CIVL Statements
	 * *********************************************************************
	 */

	/**
	 * Given a StatementNode, return a Fragment representing it. Takes a
	 * statement node where the start location and extra guard are defined
	 * elsewhere and returns the appropriate model statement.
	 * 
	 * @param scope
	 *            The scope containing this statement.
	 * @param statementNode
	 *            The statement node.
	 * @return The fragment representation of this statement.
	 */
	private Fragment translateStatementNode(Scope scope,
			StatementNode statementNode) {
		Fragment result = null;

		modelFactory.addConditionalExpressionQueue();
		switch (statementNode.statementKind()) {
		// case ASSUME:
		// result = translateAssumeNode(scope, (AssumeNode) statementNode);
		// break;
		// case ASSERT:
		// result = translateAssertNode(scope, (AssertNode) statementNode);
		// break;
		case ATOMIC:
			result = translateAtomicNode(scope, (AtomicNode) statementNode);
			break;
		case CHOOSE:
			result = translateChooseNode(scope,
					(ChooseStatementNode) statementNode);
			break;
		case CIVL_FOR: {
			CivlForNode forNode = (CivlForNode) statementNode;

			if (forNode.isParallel())
				result = translateCivlParForNode(scope, forNode);
			else
				result = translateCivlForNode(scope, forNode);
			break;
		}
		case COMPOUND:
			result = translateCompoundStatementNode(scope,
					(CompoundStatementNode) statementNode);
			break;
		case EXPRESSION:
			if (((ExpressionStatementNode) statementNode).getExpression() == null)
				result = new CommonFragment();
			else
				result = translateExpressionStatementNode(scope,
						((ExpressionStatementNode) statementNode)
								.getExpression());
			break;
		// case FOR:
		// result = translateForLoopNode(scope, (ForLoopNode) statementNode);
		// break;
		// case GOTO:
		// result = translateGotoNode(scope, (GotoNode) statementNode);
		// break;
		case IF:
			result = translateIfNode(scope, (IfNode) statementNode);
			break;
		case JUMP:
			result = translateJumpNode(scope, (JumpNode) statementNode);
			break;
		case LABELED:
			result = translateLabelStatementNode(scope,
					(LabeledStatementNode) statementNode);
			break;
		case LOOP:// either WHILE loop or DO_WHILE loop
			result = translateLoopNode(scope, (LoopNode) statementNode);
			break;
		case NULL:
			result = translateNullStatementNode(scope,
					(NullStatementNode) statementNode);
			break;
		// case RETURN:
		// result = translateReturnNode(scope, (ReturnNode) statementNode);
		// break;
		case SWITCH:
			result = translateSwitchNode(scope, (SwitchNode) statementNode);
			break;
		case WHEN:
			result = translateWhenNode(scope, (WhenNode) statementNode);
			break;
		default:
			throw new CIVLUnimplementedFeatureException("statements of type "
					+ statementNode.getClass().getSimpleName(),
					modelFactory.sourceOf(statementNode));
		}
		if (modelFactory.hasConditionalExpressions() == true) {
			result = modelFactory.refineConditionalExpressionOfStatement(
					result.uniqueFinalStatement(), result.startLocation());
		}
		modelFactory.popConditionaExpressionStack();
		if (!modelFactory.anonFragment().isEmpty()) {
			result = modelFactory.anonFragment().combineWith(result);
			modelFactory.clearAnonFragment();
		}
		return result;
	}

	private FunctionCallNode isFunctionCall(StatementNode block) {
		StatementNode statement = block;

		if (block.statementKind() == StatementKind.COMPOUND) {
			CompoundStatementNode compound = (CompoundStatementNode) block;

			if (compound.numChildren() > 1)
				return null;
			statement = (StatementNode) compound.getSequenceChild(0);
		}
		if (statement.statementKind() == StatementKind.EXPRESSION) {
			ExpressionNode expr = ((ExpressionStatementNode) statement)
					.getExpression();

			if (expr.expressionKind() == ExpressionKind.FUNCTION_CALL)
				return (FunctionCallNode) expr;
		}
		return null;
	}

	private Fragment translateCivlParForNode(Scope scope,
			CivlForNode civlForNode) {
		DeclarationListNode loopInits = civlForNode.getVariables();
		Triple<Scope, Fragment, List<Variable>> initResults = this
				.translateForLoopInitializerNode(scope, loopInits);
		CIVLSource source = modelFactory.sourceOf(civlForNode);
		CIVLSource parForBeginSource = modelFactory
				.sourceOfBeginning(civlForNode);
		CIVLSource parForEndSource = modelFactory.sourceOfEnd(civlForNode);
		VariableExpression domSizeVar = modelFactory.domSizeVariable(source,
				scope);
		CIVLArrayType procsType = typeFactory.completeArrayType(
				typeFactory.processType(), domSizeVar);
		VariableExpression parProcs = modelFactory.parProcsVariable(source,
				procsType, scope);
		StatementNode bodyNode = civlForNode.getBody();
		FunctionCallNode bodyFuncCall = this.isFunctionCall(bodyNode);
		CIVLFunction procFunc;
		CivlParForSpawnStatement parForEnter;
		Fragment result;
		CallOrSpawnStatement callWaitAll;
		Location location;
		Expression domain;
		CallOrSpawnStatement call = null;

		if (bodyFuncCall != null) {
			// $parfor(...) func(); -- no need for _par_for_proc function
			call = (CallOrSpawnStatement) this.translateFunctionCall(
					initResults.first, null, bodyFuncCall, true,
					parForEndSource);

			// modelBuilder.callStatements.put(call, value)
			procFunc = call.function();
		} else {
			CIVLSource procFuncSource = modelFactory.sourceOf(bodyNode);
			CIVLSource procFuncStartSource = modelFactory
					.sourceOfBeginning(bodyNode);
			List<Variable> loopVars = initResults.third;
			int numOfLoopVars = loopVars.size();
			List<Variable> procFuncParameters = new ArrayList<>(numOfLoopVars);

			for (int i = 0; i < numOfLoopVars; i++) {
				Variable loopVar = loopVars.get(i);
				Variable parameter = modelFactory.variable(loopVar.getSource(),
						loopVar.type(), loopVar.name(), i + 1);

				procFuncParameters.add(parameter);
			}
			procFunc = modelFactory.function(
					procFuncSource,
					modelFactory.identifier(procFuncStartSource, PAR_FUNC_NAME
							+ modelBuilder.parProcFunctions.size()),
					procFuncParameters, typeFactory.voidType(), scope, null);
			scope.addFunction(procFunc);
			modelBuilder.parProcFunctions.put(procFunc, bodyNode);
		}
		domain = this.translateExpressionNode(civlForNode.getDomain(), scope,
				true);
		result = new CommonFragment(this.elaborateDomainCall(scope, domain));
		// this.civlParForCount++;
		location = modelFactory.location(parForBeginSource, scope);
		parForEnter = modelFactory.civlParForEnterStatement(parForBeginSource,
				location, domain, domSizeVar, parProcs, procFunc);
		assert procFunc != null;
		parForEnter.setParProcFunction(procFunc);
		result = result.combineWith(new CommonFragment(parForEnter));
		location = modelFactory.location(parForEndSource, scope);
		callWaitAll = modelFactory.callOrSpawnStatement(parForEndSource,
				location, true, modelFactory.waitallFunctionPointer(),
				Arrays.asList(this.arrayToPointer(parProcs), domSizeVar), null);
		callWaitAll.setGuard(modelFactory.systemGuardExpression(callWaitAll));
		result = result.combineWith(new CommonFragment(callWaitAll));
		return result;
	}

	private Fragment translateCivlForNode(Scope scope, CivlForNode civlForNode) {
		DeclarationListNode loopInits = civlForNode.getVariables();
		Fragment nextInDomain, result;
		List<Variable> loopVariables;
		ExpressionNode domainNode = civlForNode.getDomain();
		Expression domain;
		Expression domainGuard;
		Variable literalDomCounter;
		Triple<Scope, Fragment, List<Variable>> initResults = this
				.translateForLoopInitializerNode(scope, loopInits);
		Location location;
		CIVLSource source = modelFactory.sourceOf(civlForNode);
		int dimension;
		Statement elaborateCall;

		scope = initResults.first;
		// Create a loop counter variable for the for loop.
		literalDomCounter = modelFactory.variable(source, typeFactory
				.integerType(), modelFactory.getLiteralDomCounterIdentifier(
				source, this.literalDomForCounterCount), scope.numVariables());
		this.literalDomForCounterCount++;
		scope.addVariable(literalDomCounter);
		loopVariables = initResults.third;
		location = modelFactory.location(
				modelFactory.sourceOfBeginning(civlForNode), scope);
		domain = this.translateExpressionNode(civlForNode.getDomain(), scope,
				true);
		elaborateCall = this.elaborateDomainCall(scope, domain);
		dimension = ((CIVLCompleteDomainType) domain.getExpressionType())
				.getDimension();
		if (dimension != loopVariables.size()) {
			throw new CIVLSyntaxException(
					"The number of loop variables for $for does NOT match "
							+ "the dimension of the domain " + domain + ":\n"
							+ "number of loop variables: "
							+ loopVariables.size() + "\n" + "dimension of "
							+ domain + ": " + dimension, source);
		}
		domainGuard = modelFactory.domainGuard(
				modelFactory.sourceOf(domainNode), loopVariables,
				literalDomCounter, domain);
		location = modelFactory.location(
				modelFactory.sourceOfBeginning(civlForNode), scope);
		nextInDomain = modelFactory.civlForEnterFragment(
				modelFactory.sourceOfBeginning(civlForNode), location, domain,
				initResults.third, literalDomCounter);
		result = this.composeLoopFragmentWorker(scope,
				modelFactory.sourceOfBeginning(domainNode),
				modelFactory.sourceOfEnd(domainNode), domainGuard,
				nextInDomain, civlForNode.getBody(), null, false);
		return new CommonFragment(elaborateCall).combineWith(result);
	}

	/**
	 * If the given CIVL expression e has array type, this returns the
	 * expression &e[0]. Otherwise returns e unchanged.<br>
	 * This method should be called on every LHS expression e when it is used in
	 * a place where a RHS expression is called for, except in the following
	 * cases: (1) e is the first argument to the SUBSCRIPT operator (i.e., e
	 * occurs in the context e[i]), or (2) e is the argument to the "sizeof"
	 * operator.<br>
	 * note: argument to & should never have array type.
	 * 
	 * @param array
	 *            any CIVL expression e
	 * @return either the original expression or &e[0]
	 */
	protected Expression arrayToPointer(Expression array) {
		CIVLType type = array.getExpressionType();

		if (array instanceof ArrayLiteralExpression)
			return array;
		if (type.isArrayType()) {
			CIVLSource source = array.getSource();
			Expression zero = modelFactory.integerLiteralExpression(source,
					BigInteger.ZERO);
			LHSExpression subscript = modelFactory.subscriptExpression(source,
					(LHSExpression) array, zero);

			return modelFactory.addressOfExpression(source, subscript);
		}
		return array;
	}

	/**
	 * Sometimes an assignment is actually modeled as a fork or function call
	 * with an optional left hand side argument. Catch these cases.
	 * 
	 * @param source
	 *            the CIVL source information of the assign node
	 * @param location
	 *            The start location for this assign.
	 * @param lhs
	 *            Model expression for the left hand side of the assignment.
	 * @param rhsNode
	 *            AST expression for the right hand side of the assignment.
	 * @param isInitializer
	 *            is this assignment part of a variable initializer?
	 * @param scope
	 *            The scope containing this assignment.
	 * @return The model representation of the assignment, which might also be a
	 *         fork statement or function call.
	 */
	private Fragment assignStatement(CIVLSource source, LHSExpression lhs,
			ExpressionNode rhsNode, boolean isInitializer, Scope scope) {
		Statement assign = null;
		Location location;

		if (isCompleteMallocExpression(rhsNode)) {
			location = modelFactory.location(lhs.getSource(), scope);
			assign = mallocStatement(source, location, lhs, (CastNode) rhsNode,
					scope);
			return new CommonFragment(assign);
		} else if (rhsNode instanceof FunctionCallNode
				|| rhsNode instanceof SpawnNode) {
			FunctionCallNode functionCallNode;
			boolean isCall;

			if (rhsNode instanceof FunctionCallNode) {
				functionCallNode = (FunctionCallNode) rhsNode;
				isCall = true;
			} else {
				functionCallNode = ((SpawnNode) rhsNode).getCall();
				isCall = false;
			}

			if (rhsNode.getNumConversions() > 0) {
				Fragment result;
				CIVLType type = this.translateABCType(source, scope,
						rhsNode.getInitialType());
				Variable tmpVar = this.modelFactory.newAnonymousVariable(
						source, scope, type);
				LHSExpression tmpLhs = this.modelFactory.variableExpression(
						source, tmpVar);
				Expression castTmp;

				assign = translateFunctionCall(scope, tmpLhs, functionCallNode,
						isCall, source);
				result = new CommonFragment(assign);
				tmpLhs = this.modelFactory.variableExpression(source, tmpVar);
				castTmp = this
						.applyConversions(scope, functionCallNode, tmpLhs);
				assign = modelFactory.assignStatement(source,
						this.modelFactory.location(source, scope), lhs,
						castTmp, false);
				result.addNewStatement(assign);
				return result;
			} else {
				assign = translateFunctionCall(scope, lhs, functionCallNode,
						isCall, source);
				return new CommonFragment(assign);
			}

		} else {
			Expression rhs;

			rhs = translateExpressionNode(rhsNode, scope, true);
			location = modelFactory.location(lhs.getSource(), scope);
			assign = modelFactory.assignStatement(source, location, lhs, rhs,
					isInitializer);
			this.normalizeAssignment((AssignStatement) assign);
			return new CommonFragment(assign);
		}
	}

	/**
	 * Translate a FunctionCall node into a call or spawn statement
	 * 
	 * @param location
	 *            The origin location for this statement. Must be non-null.
	 * @param scope
	 *            The scope containing this statement. Must be non-null.
	 * @param callNode
	 *            The ABC node representing the function called or spawned. Must
	 *            be non-null.
	 * @param lhs
	 *            The left-hand-side expression, where the value of the function
	 *            call or process ID resulting from the spawn is stored. May be
	 *            null.
	 * @param isCall
	 *            True when the node is a call node, otherwise the node is a
	 *            spawn node
	 * @return the CallOrSpawnStatement
	 */
	private CallOrSpawnStatement callOrSpawnStatement(Scope scope,
			Location location, FunctionCallNode callNode, LHSExpression lhs,
			List<Expression> arguments, boolean isCall, CIVLSource source) {
		ExpressionNode functionExpression = ((FunctionCallNode) callNode)
				.getFunction();
		CallOrSpawnStatement result;
		Function callee;

		if (isMallocCall(callNode))
			throw new CIVLException(
					"$malloc can only occur in a cast expression",
					modelFactory.sourceOf(callNode));
		if (functionExpression instanceof IdentifierExpressionNode) {
			Entity entity = ((IdentifierExpressionNode) functionExpression)
					.getIdentifier().getEntity();

			switch (entity.getEntityKind()) {
			case FUNCTION:
				callee = (Function) entity;
				result = modelFactory.callOrSpawnStatement(source, location,
						isCall, null, arguments, null);
				break;
			case VARIABLE:
				Expression function = this.translateExpressionNode(
						functionExpression, scope, true);

				callee = null;
				result = modelFactory.callOrSpawnStatement(source, location,
						isCall, function, arguments, null);
				// added function guard expression since the function could be a
				// system function which has an outstanding guard, only when it
				// is a call statement
				if (isCall)
					result.setGuard(modelFactory.functionGuardExpression(
							source, function, arguments));
				break;
			default:
				throw new CIVLUnimplementedFeatureException(
						"Function call must use identifier of variables or functions for now: "
								+ functionExpression.getSource());
			}
		} else {
			Expression function = this.translateExpressionNode(
					functionExpression, scope, true);

			callee = null;
			result = modelFactory.callOrSpawnStatement(source, location,
					isCall, function, arguments, null);
			// added function guard expression since the function could be a
			// system function which has an outstanding guard, only when it
			// is a call statement
			if (isCall)
				result.setGuard(modelFactory.functionGuardExpression(source,
						function, arguments));
		}
		// throw new CIVLUnimplementedFeatureException(
		// "Function call must use identifier for now: "
		// + functionExpression.getSource());
		result.setLhs(lhs);
		if (callee != null)
			modelBuilder.callStatements.put(result, callee);
		return result;
	}

	/**
	 * Composes a loop fragment.
	 * 
	 * @param loopScope
	 *            The scope of the loop
	 * @param condStartSource
	 *            The beginning source of the loop condition
	 * @param condEndSource
	 *            The ending source of the loop condition
	 * @param condition
	 *            The loop condition
	 * @param bodyPrefix
	 *            The fragment before entering the loop
	 * @param loopBodyNode
	 *            The body statement node of the loop
	 * @param incrementer
	 *            The incrementer fragment of the loop
	 * @param isDoWhile
	 *            If this is a do-while loop
	 * @return
	 */
	private Fragment composeLoopFragmentWorker(Scope loopScope,
			CIVLSource condStartSource, CIVLSource condEndSource,
			Expression condition, Fragment bodyPrefix,
			StatementNode loopBodyNode, Fragment incrementer, boolean isDoWhile) {
		Set<Statement> continues, breaks, switchExits;
		Fragment beforeCondition, loopEntrance, loopBody, loopExit, result;
		Location loopEntranceLocation, continueLocation;
		Pair<Fragment, Expression> refineConditional;

		refineConditional = modelFactory.refineConditionalExpression(loopScope,
				condition, condStartSource, condStartSource);
		beforeCondition = refineConditional.left;
		condition = refineConditional.right;
		try {
			condition = modelFactory.booleanExpression(condition);
		} catch (ModelFactoryException err) {
			throw new CIVLSyntaxException(
					"The condition of the loop statement "
							+ condition
							+ " is of "
							+ condition.getExpressionType()
							+ " type which cannot be converted to boolean type.",
					condition.getSource());
		}
		loopEntranceLocation = modelFactory.location(condition.getSource(),
				loopScope);
		// incrementer comes after the loop body
		loopEntrance = new CommonFragment(modelFactory.loopBranchStatement(
				condition.getSource(), loopEntranceLocation, condition, true));
		// the loop entrance location is the same as the loop exit location
		loopExit = new CommonFragment(modelFactory.loopBranchStatement(
				condition.getSource(), loopEntranceLocation, modelFactory
						.unaryExpression(condition.getSource(),
								UNARY_OPERATOR.NOT, condition), false));
		if (beforeCondition != null) {
			loopEntrance = beforeCondition.combineWith(loopEntrance);
		}
		functionInfo.addContinueSet(new LinkedHashSet<Statement>());
		functionInfo.addBreakSet(new LinkedHashSet<Statement>());
		loopBody = translateStatementNode(loopScope, loopBodyNode);
		if (bodyPrefix != null)
			loopBody = bodyPrefix.combineWith(loopBody);
		continues = functionInfo.popContinueStack();
		// if there is no incrementer statement, continue statements will go to
		// the loop entrance/exit location
		if (incrementer != null) {
			continueLocation = incrementer.startLocation();
		} else
			continueLocation = loopEntrance.startLocation();
		for (Statement s : continues) {
			s.setTarget(continueLocation);
		}
		// loopEntrance.startLocation().setLoopPossible(true);
		if (incrementer != null)
			loopBody = loopBody.combineWith(incrementer);
		// loop entrance comes before the loop body, P.S. loopExit is "combined"
		// implicitly because its start location is the same as loopEntrance
		loopBody = loopBody.combineWith(loopEntrance);
		// initially loop entrance comes before the loopBody. Now we'll have
		// loopBody -> loopEntrance -> loopBody and the loop is formed.
		result = loopEntrance.combineWith(loopBody);
		// for do while, mark the loopbody's start location as the start
		// location of the resulting fragment
		if (isDoWhile)
			result.setStartLocation(loopBody.startLocation());
		// break statements will go out of the loop, and thus is considered as
		// one of the last statement of the fragment
		breaks = functionInfo.popBreakStack();
		switchExits = breaks;
		switchExits.addAll(loopExit.finalStatements());
		result.setFinalStatements(switchExits);
		return result;
	}

	/**
	 * Helper method for translating for-loop and while-loop statement nodes
	 * Translate a loop structure into a fragment of CIVL statements
	 * 
	 * @param loopScope
	 *            The scope containing the loop body.
	 * @param conditionNode
	 *            The loop condition which is an expression node
	 * @param loopBodyNode
	 *            The body of the loop which is a statement node
	 * @param incrementerNode
	 *            The incrementer which is an expression node, null for while
	 *            loop
	 * @param isDoWhile
	 *            True iff the loop is a do-while loop. Always false for for
	 *            loop and while loop.
	 * @return the fragment of the loop structure
	 */
	private Fragment composeLoopFragment(Scope loopScope,
			ExpressionNode conditionNode, StatementNode loopBodyNode,
			ExpressionNode incrementerNode, boolean isDoWhile) {
		Expression condition;
		Fragment incrementer = null;
		CIVLSource conditionStart, conditionEnd;

		if (conditionNode == null) {
			conditionStart = modelFactory.sourceOfBeginning(loopBodyNode);
			conditionEnd = modelFactory.sourceOfBeginning(loopBodyNode);
			condition = modelFactory.trueExpression(conditionStart);
		} else {
			conditionStart = modelFactory.sourceOfBeginning(conditionNode);
			conditionEnd = modelFactory.sourceOfEnd(conditionNode);
			condition = translateExpressionNode(conditionNode, loopScope, true);
		}
		if (incrementerNode != null)
			incrementer = translateExpressionStatementNode(loopScope,
					incrementerNode);
		return this.composeLoopFragmentWorker(loopScope, conditionStart,
				conditionEnd, condition, null, loopBodyNode, incrementer,
				isDoWhile);
	}

	// how to process individual block elements?
	// int x: INTEGER or STRING -> universe.integer
	// real x: INTEGER or DOUBLE or STRING -> universe.real
	// String x: STRING
	// boolean x : BOOLEAN
	// else no can do yet
	// ["55", "55"]
	/**
	 * Translate command line constants into CIVL literal expression
	 * 
	 * @param variable
	 *            The variable
	 * @param constant
	 *            The constant value object
	 * @return the literal expression of the constant
	 * @throws CommandLineException
	 */
	private LiteralExpression constant(Variable variable, Object constant)
			throws CommandLineException {
		CIVLType type = variable.type();
		CIVLSource source = variable.getSource();

		if (type instanceof CIVLPrimitiveType) {
			PrimitiveTypeKind kind = ((CIVLPrimitiveType) type)
					.primitiveTypeKind();

			switch (kind) {
			case BOOL:
				if (constant instanceof Boolean)
					return modelFactory.booleanLiteralExpression(source,
							(boolean) constant);
				else
					throw new CommandLineException(
							"Expected boolean value for variable " + variable
									+ " but saw " + constant);
			case INT:
				if (constant instanceof Integer)
					return modelFactory.integerLiteralExpression(source,
							new BigInteger(((Integer) constant).toString()));
				if (constant instanceof String)
					return modelFactory.integerLiteralExpression(source,
							new BigInteger((String) constant));
				else
					throw new CommandLineException(
							"Expected integer value for variable " + variable
									+ " but saw " + constant);
			case REAL:
				if (constant instanceof Integer)
					return modelFactory.realLiteralExpression(source,
							new BigDecimal(((Integer) constant).toString()));
				if (constant instanceof Double)
					return modelFactory.realLiteralExpression(source,
							new BigDecimal(((Double) constant).toString()));
				if (constant instanceof String)
					return modelFactory.realLiteralExpression(source,
							new BigDecimal((String) constant));
				else
					throw new CommandLineException(
							"Expected real value for variable " + variable
									+ " but saw " + constant);
			default:
			}
		} else {
			if (type.isArrayType()) {
				CIVLArrayType arrayType = (CIVLArrayType) type;
				CIVLType elementType = arrayType.elementType();

				if (elementType.isCharType()) {

				}

			}
		}
		throw new CIVLUnimplementedFeatureException(
				"Specification of initial value not of integer, real, or boolean type",
				variable);
	}

	/**
	 * Checks if a given fragment (which is to be used as the function body of
	 * some function) contains a return statement. It returns true iff all
	 * possible executions have return statements.
	 * 
	 * @param functionBody
	 *            The fragment to be checked.
	 * @return True iff a return statement can be reached back from the last
	 *         statement.
	 */
	private boolean containsReturn(Fragment functionBody) {
		Set<Statement> lastStatements = functionBody.finalStatements();
		Statement uniqueLastStatement;

		if (functionBody == null || functionBody.isEmpty())
			return false;
		if (lastStatements.size() > 1) {
			for (Statement statement : lastStatements) {
				if (!(statement instanceof ReturnStatement))
					return false;
			}
			return true;
		}
		uniqueLastStatement = functionBody.uniqueFinalStatement();
		if (uniqueLastStatement.source().getNumOutgoing() == 1) {
			Location lastLocation = uniqueLastStatement.source();
			Set<Integer> locationIds = new HashSet<Integer>();

			while (lastLocation.atomicKind() == AtomicKind.ATOMIC_EXIT
					|| lastLocation.atomicKind() == AtomicKind.ATOM_EXIT) {
				locationIds.add(lastLocation.id());
				if (lastLocation.getNumIncoming() == 1) {
					lastLocation = lastLocation.getIncoming(0).source();
					if (locationIds.contains(lastLocation.id()))
						return false;
				} else {
					return false;
				}
			}
			if (lastLocation.getNumOutgoing() == 1
					&& lastLocation.getOutgoing(0) instanceof ReturnStatement) {
				return true;
			}
		}
		return false;
	}

	/**
	 * @param fileName
	 *            The name of a certain file
	 * @return File name without extension
	 */
	private String fileNameWithoutExtension(String fileName) {
		int dotIndex = fileName.lastIndexOf('.');
		String libName;

		libName = fileName.substring(0, dotIndex);
		return libName;
	}

	/**
	 * Is the ABC expression node an expression of the form
	 * <code>(t)$malloc(...)</code>? I.e., a cast expression for which the
	 * argument is a malloc call?
	 * 
	 * @param node
	 *            an expression node
	 * @return true iff this is a cast of a malloc call
	 */
	private boolean isCompleteMallocExpression(ExpressionNode node) {
		if (node instanceof CastNode) {
			ExpressionNode argumentNode = ((CastNode) node).getArgument();

			return isMallocCall(argumentNode);
		}
		return false;
	}

	/**
	 * Is the ABC expression node a call to the function "$malloc"?
	 * 
	 * @param node
	 *            The expression node to be checked.
	 * @return true iff node is a function call to node to a function named
	 *         "$malloc"
	 */
	private boolean isMallocCall(ExpressionNode node) {
		if (node instanceof FunctionCallNode) {
			ExpressionNode functionNode = ((FunctionCallNode) node)
					.getFunction();

			if (functionNode instanceof IdentifierExpressionNode) {
				String functionName = ((IdentifierExpressionNode) functionNode)
						.getIdentifier().name();

				if ("$malloc".equals(functionName)
						|| "malloc".equals(functionName))
					return true;
			}
		}
		return false;
	}

	/**
	 * Translate a cast node into a malloc statement
	 * 
	 * @param source
	 *            The CIVL source
	 * @param location
	 *            The location
	 * @param lhs
	 *            The left-hand-side expression
	 * @param castNode
	 *            The node of the malloc statement
	 * @param scope
	 *            The scope
	 * @return the malloc statement
	 */
	private MallocStatement mallocStatement(CIVLSource source,
			Location location, LHSExpression lhs, CastNode castNode, Scope scope) {
		TypeNode typeNode = castNode.getCastType();
		CIVLType pointerType = translateABCType(
				modelFactory.sourceOf(typeNode), scope, typeNode.getType());
		FunctionCallNode callNode = (FunctionCallNode) castNode.getArgument();
		int mallocId = modelBuilder.mallocStatements.size();
		Expression scopeExpression;
		Expression sizeExpression;
		CIVLType elementType;
		MallocStatement result;

		if (!pointerType.isPointerType())
			throw new CIVLException(
					"result of $malloc/malloc not cast to pointer type", source);
		elementType = ((CIVLPointerType) pointerType).baseType();
		if (elementType.isVoidType()) {
			throw new CIVLSyntaxException(
					"missing cast to non-void pointer type around malloc expression: "
							+ "CIVL-C requires that malloc expressions be enclosed in a cast to a pointer to a non-void type, "
							+ "such as (double*)$malloc($here, n*sizeof(double))",
					source);
		}
		if (callNode.getNumberOfArguments() == 1) {
			scopeExpression = modelFactory.hereOrRootExpression(source, true);
			sizeExpression = translateExpressionNode(callNode.getArgument(0),
					scope, true);
		} else {
			scopeExpression = translateExpressionNode(callNode.getArgument(0),
					scope, true);
			sizeExpression = translateExpressionNode(callNode.getArgument(1),
					scope, true);
		}
		result = modelFactory.mallocStatement(source, location, lhs,
				elementType, scopeExpression, sizeExpression, mallocId, null);
		modelBuilder.mallocStatements.add(result);
		return result;
	}

	private void normalizeAssignment(AssignStatement assign) {
		LHSExpression lhs = assign.getLhs();
		Expression rhs = assign.rhs();

		if (rhs instanceof BinaryExpression) {
			BinaryExpression binary = (BinaryExpression) rhs;
			Expression leftOperand = binary.left(), rightOperand = binary
					.right();

			if (leftOperand.equals(lhs))
				binary.setAssignToLeft(true);
			else if (rightOperand.equals(lhs)) {
				binary.setAssignToLeft(binary.switchOperands());
			}
		}
	}

	/**
	 * Sometimes an assignment is actually modeled as a spawn or function call
	 * with an optional left hand side argument. Catch these cases.
	 * 
	 * Precondition: assignNode.getOperator() == ASSIGN;
	 * 
	 * @param assignNode
	 *            The assign node to be translated.
	 * @param scope
	 *            The scope containing this assignment.
	 * @return The model representation of the assignment, which might also be a
	 *         fork statement or function call.
	 */
	private Fragment translateAssignNode(Scope scope, OperatorNode assignNode) {
		ExpressionNode lhs = assignNode.getArgument(0);
		ExpressionNode rhs = assignNode.getArgument(1);
		Expression leftExpression;

		// this.isLHS = true;
		leftExpression = translateExpressionNode(lhs, scope, true);
		// this.isLHS = false;
		assert assignNode.getOperator() == Operator.ASSIGN;
		if (!(leftExpression instanceof LHSExpression))
			throw new CIVLInternalException("expected LHS expression, not "
					+ leftExpression, modelFactory.sourceOf(lhs));
		if (leftExpression instanceof VariableExpression) {
			Variable lhsVariable = ((VariableExpression) leftExpression)
					.variable();

			if (lhsVariable.isInput())
				throw new CIVLSyntaxException(
						"attempt to modify the input variable "
								+ leftExpression, modelFactory.sourceOf(lhs));
			if (lhsVariable.isConst())
				throw new CIVLSyntaxException(
						"attempt to modify the constant variable "
								+ leftExpression, modelFactory.sourceOf(lhs));
		}
		return assignStatement(modelFactory.sourceOfSpan(lhs, rhs),
				(LHSExpression) leftExpression, rhs, false, scope);
	}

	// /**
	// * Translate an assume node into a fragment of CIVL statements
	// *
	// * @param scope
	// * The scope containing this statement.
	// * @param assumeNode
	// * The assume node to be translated.
	// * @return the fragment
	// */
	// private Fragment translateAssumeNode(Scope scope, AssumeNode assumeNode)
	// {
	// Expression expression;
	// Location location;
	// Fragment result;
	//
	// expression = translateExpressionNode(assumeNode.getExpression(), scope,
	// true);
	// location = modelFactory.location(
	// modelFactory.sourceOfBeginning(assumeNode), scope);
	// result = modelFactory.assumeFragment(modelFactory.sourceOf(assumeNode),
	// location, expression);
	// result = result.combineWith(accuracyAssumptionBuilder
	// .accuracyAssumptions(expression, scope));
	// return result;
	// }

	// /**
	// *
	// * Translate an assert node into a fragment of CIVL statements
	// *
	// * @param scope
	// * The scope containing this statement.
	// * @param assertNode
	// * The assert node to be translated.
	// * @return the result fragment
	// */
	// private Fragment translateAssertNode(Scope scope, AssertNode assertNode)
	// {
	// Expression expression;
	// Location location;
	// Fragment result;
	// Expression[] explanation = null;
	// SequenceNode<ExpressionNode> explanationNode = assertNode
	// .getExplanation();
	//
	// expression = translateExpressionNode(assertNode.getCondition(), scope,
	// true);
	// try {
	// expression = modelFactory.booleanExpression(expression);
	// } catch (ModelFactoryException e) {
	// throw new CIVLSyntaxException(
	// "The expression of the $assert statement "
	// + expression
	// + " is of "
	// + expression.getExpressionType()
	// + " type which cannot be converted to boolean type.",
	// assertNode.getSource());
	// }
	// location = modelFactory.location(
	// modelFactory.sourceOfBeginning(assertNode), scope);
	// if (explanationNode != null) {
	// int numArgs = explanationNode.numChildren();
	// List<Expression> args = new ArrayList<>(numArgs);
	//
	// explanation = new Expression[numArgs];
	// for (int i = 0; i < numArgs; i++) {
	// Expression arg = translateExpressionNode(
	// explanationNode.getSequenceChild(i), scope, true);
	//
	// arg = this.arrayToPointer(arg);
	// args.add(arg);
	// }
	// args.toArray(explanation);
	// }
	// result = modelFactory.assertFragment(modelFactory.sourceOf(assertNode),
	// location, expression, explanation);
	// return result;
	// }

	/**
	 * @param node
	 *            The AST node
	 * @param scope
	 *            The scope
	 * @param location
	 *            The location
	 * @return The fragment of statements translated from the AST node
	 */
	private Fragment translateASTNode(ASTNode node, Scope scope,
			Location location) {
		Fragment result = null;

		switch (node.nodeKind()) {
		case VARIABLE_DECLARATION:
			try {
				result = translateVariableDeclarationNode(location, scope,
						(VariableDeclarationNode) node);
				if (!modelFactory.anonFragment().isEmpty()) {
					result = modelFactory.anonFragment().combineWith(result);
					modelFactory.clearAnonFragment();
				}
			} catch (CommandLineException e) {
				throw new CIVLInternalException(
						"Saw input variable outside of root scope",
						modelFactory.sourceOf(node));
			}
			break;
		case PRAGMA:// ignored pragma
			result = new CommonFragment();
			break;
		case TYPEDEF:
			// TypedefDeclarationNode node has to be processed separately from
			// StructureOrUnionTypeNode, because TypedefDeclarationNode is not a
			// sub-type of TypeNode but the one returned by
			// TypedefDeclarationNode.getTypeNode() is.
			result = translateCompoundTypeNode(location, scope,
					((TypedefDeclarationNode) node).getTypeNode());
			break;
		case FUNCTION_DEFINITION:
			FunctionDefinitionNode functionDefinitionNode = (FunctionDefinitionNode) node;
			if (functionDefinitionNode.getName().equals("main")) {
				// TODO arguments to main() become arguments to the system
				// function; specified by command line, after the .cvl file
				// name; think about how to initialize them.
				modelBuilder.mainFunctionNode = functionDefinitionNode;
			} else
				translateFunctionDeclarationNode(functionDefinitionNode, scope,
						null);
			break;
		case FUNCTION_DECLARATION:
			translateFunctionDeclarationNode((FunctionDeclarationNode) node,
					scope, null);
			break;
		case STATEMENT:
			result = translateStatementNode(scope, (StatementNode) node);
			break;
		case TYPE:
			TypeNode typeNode = (TypeNode) node;

			switch (typeNode.kind()) {
			case STRUCTURE_OR_UNION:
			case ENUMERATION:
				result = translateCompoundTypeNode(location, scope,
						(TypeNode) node);
				return result;
			default:
			}
			// if not structure or union type or enumeration type, then execute
			// default
			// case to throw an exception
		default:
			if (scope.id() == modelBuilder.systemScope.id())
				throw new CIVLInternalException("Unsupported declaration type",
						modelFactory.sourceOf(node));
			else
				throw new CIVLUnimplementedFeatureException(
						"Unsupported block element",
						modelFactory.sourceOf(node));
		}
		return result;
	}

	private CIVLType translateABCEnumerationType(CIVLSource source,
			Scope scope, EnumerationType enumType) {
		String name = enumType.getTag();
		int numOfEnumerators = enumType.getNumEnumerators();
		BigInteger currentValue = BigInteger.ZERO;
		Map<String, BigInteger> valueMap = new LinkedHashMap<>(numOfEnumerators);

		if (name == null) {
			throw new CIVLInternalException(
					"Anonymous enum encountered, which should already "
							+ "been handled by ABC", source);
		}
		for (Enumerator enumerator : enumType.getEnumerators()) {
			String member = enumerator.getName();
			Value abcValue = enumerator.getValue();
			BigInteger value;

			if (abcValue != null) {
				if (abcValue instanceof IntegerValue) {
					value = ((IntegerValue) abcValue).getIntegerValue();
				} else if (abcValue instanceof CharacterValue) {
					value = BigInteger.valueOf(((CharacterValue) abcValue)
							.getCharacter().getCharacters()[0]);
				} else
					throw new CIVLSyntaxException(
							"Only integer or char constant can be used in enumerators.",
							source);
			} else {
				value = currentValue;
			}
			valueMap.put(member, value);
			currentValue = value.add(BigInteger.ONE);
		}
		return typeFactory.enumType(name, valueMap);
	}

	/**
	 * Translate an ABC AtomicNode, which represents either an $atomic block or
	 * an $atom block, dependent on {@link AtomicNode#isDeterministic()}.
	 * 
	 * @param scope
	 * @param statementNode
	 * @return
	 */
	private Fragment translateAtomicNode(Scope scope, AtomicNode atomicNode) {
		StatementNode bodyNode = atomicNode.getBody();
		Fragment bodyFragment;
		Location start = modelFactory.location(
				modelFactory.sourceOfBeginning(atomicNode), scope);
		Location end = modelFactory.location(
				modelFactory.sourceOfEnd(atomicNode), scope);
		Location firstStmtLoc, atomicEnterLoc;
		Iterator<Statement> firstStmtsIter;
		Expression guard = null;

		if (atomicNode.isAtom())
			this.atomCount++;
		else
			this.atomicCount++;
		bodyFragment = translateStatementNode(scope, bodyNode);
		firstStmtLoc = bodyFragment.startLocation();
		// translate of the first statement guard:
		// stackTopLoc = modelBuilder.peekChooseGuardLocaton();
		// if (stackTopLoc != null && stackTopLoc.id() == firstStmtLoc.id()) {
		// assert firstStmtLoc.getNumOutgoing() == 1;
		// guard = modelBuilder.popChooseGuard();
		// modelBuilder.clearChooseGuard();
		// } else {
		firstStmtsIter = firstStmtLoc.outgoing().iterator();
		while (firstStmtsIter.hasNext()) {
			Statement currStmt = firstStmtsIter.next();

			guard = (guard == null) ? currStmt.guard() : modelFactory
					.binaryExpression(currStmt.getSource(),
							BINARY_OPERATOR.AND, guard, currStmt.guard());
		}
		// }
		if (atomicNode.isAtom())
			this.atomCount--;
		else
			this.atomicCount--;
		bodyFragment = modelFactory.atomicFragment(atomicNode.isAtom(),
				bodyFragment, start, end);
		atomicEnterLoc = bodyFragment.startLocation();
		assert atomicEnterLoc.getNumOutgoing() == 1 : "ENTER_ATOMIC location "
				+ "should only have exactly one outgoing statement.";
		assert guard != null;
		atomicEnterLoc.getSoleOutgoing().setGuard(guard);
		return bodyFragment;
	}

	/**
	 * Translate a choose node into a fragment that has multiple outgoing
	 * statements from its start location
	 * 
	 * @param scope
	 *            The scope
	 * @param chooseStatementNode
	 *            The choose statement node
	 * @return the fragment of the choose statements
	 */
	private Fragment translateChooseNode(Scope scope,
			ChooseStatementNode chooseStatementNode) {
		CIVLSource startSource = modelFactory
				.sourceOfBeginning(chooseStatementNode);
		Location startLocation = modelFactory.location(startSource, scope);
		int defaultOffset = 0;
		Fragment result = new CommonFragment();
		Expression defaultGuard = null; // guard of default cqse
		Expression wholeGuard = null; // guard of wholse statement
		NoopStatement insertedNoop;

		if (chooseStatementNode.getDefaultCase() != null) {
			defaultOffset = 1;
		}
		result.setStartLocation(startLocation);
		for (int i = 0; i < chooseStatementNode.numChildren() - defaultOffset; i++) {
			StatementNode childNode = chooseStatementNode.getSequenceChild(i);
			Fragment caseFragment = translateStatementNode(scope, childNode);
			Expression caseGuard;

			if (this.containsHereConstant(caseFragment.startLocation())) {
				throw new CIVLSyntaxException(
						"the first (recursively) primitive statement "
								+ "of a clause of $choose should not use $here",
						caseFragment.startLocation().getSource());
			}
			caseGuard = this.factorOutGuards(caseFragment.startLocation());
			caseFragment.updateStartLocation(startLocation);
			result.addFinalStatementSet(caseFragment.finalStatements());
			wholeGuard = this.disjunction(wholeGuard, caseGuard);
		}
		if (!modelFactory.isTrue(wholeGuard)) {
			if (chooseStatementNode.getDefaultCase() != null) {
				Fragment defaultFragment = translateStatementNode(scope,
						chooseStatementNode.getDefaultCase());

				if (this.containsHereConstant(defaultFragment.startLocation())) {
					throw new CIVLSyntaxException(
							"the first (recursively) primitive statement "
									+ "of a clause of $choose should not use $here",
							defaultFragment.startLocation().getSource());
				}
				defaultGuard = modelFactory.unaryExpression(
						wholeGuard.getSource(), UNARY_OPERATOR.NOT, wholeGuard);
				defaultFragment.addGuardToStartLocation(defaultGuard,
						modelFactory);
				defaultFragment.updateStartLocation(startLocation);
				result.addFinalStatementSet(defaultFragment.finalStatements());
				wholeGuard = modelFactory.trueExpression(startSource);
			}
		}
		assert wholeGuard != null;
		// insert noop at the beginning the fragment so that the guard of the
		// start location will be true;
		result = insertNoopAtBeginning(startSource, scope, result);
		result.startLocation().getSoleOutgoing().setGuard(wholeGuard);
		insertedNoop = (NoopStatement) result.startLocation().getSoleOutgoing();
		insertedNoop.setRemovable();
		return result;
	}

	private Fragment insertNoopAtBeginning(CIVLSource source, Scope scope,
			Fragment old) {
		Location start = modelFactory.location(source, scope);
		NoopStatement noop;
		Fragment noopFragment;

		noop = modelFactory.noopStatementTemporary(source, start);
		noopFragment = new CommonFragment(noop);
		return noopFragment.combineWith(old);
	}

	/**
	 * checks if any outgoing statement of the given location uses the $here
	 * constant.
	 * 
	 * @param location
	 * @return
	 */
	private boolean containsHereConstant(Location location) {
		for (Statement stmt : location.outgoing()) {
			if (stmt.containsHere())
				return true;
		}
		return false;
	}

	/**
	 * factors out the guards of the outgoing statements of a location in
	 * disjunction.
	 * 
	 * For example, if the location has two outgoing statements: [x>2] s1; [x<6]
	 * s2; then the result is (x>2 || x<6).
	 * 
	 * If the location has exactly one outgoing statement: [x<10] s; then the
	 * result is (x<10).
	 * 
	 * This method serves as a helper function for $choose.
	 * 
	 * @param location
	 * @return
	 */
	private Expression factorOutGuards(Location location) {
		Expression guard = null;
		Iterator<Statement> iter = location.outgoing().iterator();

		while (iter.hasNext()) {
			Expression statementGuard = iter.next().guard();

			guard = this.disjunction(guard, statementGuard);
		}
		return guard;
	}

	/**
	 * Computes the disjunction of two boolean expressions. The left could be
	 * NULL but the right couldn't.
	 * 
	 * @param left
	 * @param right
	 * @return
	 */
	private Expression disjunction(Expression left, Expression right) {
		if (left == null)
			return right;
		if (modelFactory.isTrue(left))
			return left;
		if (modelFactory.isTrue(right))
			return right;
		return modelFactory.binaryExpression(
				modelFactory.sourceOfSpan(left.getSource(), right.getSource()),
				BINARY_OPERATOR.OR, left, right);
	}

	/**
	 * Translates a compound statement.
	 * <p>
	 * Tagged entities can have state and require special handling.
	 * <p>
	 * When perusing compound statements or external defs, when you come across
	 * a typedef, or complete struct or union def, we might need to create a
	 * variable if the type has some state, as
	 * {@link ModelBuilderWorker#translateCompoundTypeNode}.
	 * <p>
	 * when processing a variable decl: if variable has compound type (array or
	 * struct), insert statement (into beginning of current compound statement)
	 * saying "v = InitialValue[v]". then insert the variable's initializer if
	 * present.
	 * 
	 * @param scope
	 *            The scope that contains this compound node
	 * @param statementNode
	 *            The compound statement node
	 * @return the fragment of the compound statement node
	 */
	private Fragment translateCompoundStatementNode(Scope scope,
			CompoundStatementNode statementNode) {
		Scope newScope;
		Location location;
		// indicates whether the location field has been used:
		boolean usedLocation = false;
		Fragment result = new CommonFragment();
		boolean newScopeNeeded = this.needsNewScope(statementNode);

		// // In order to eliminate unnecessary scopes, do this loop twice.
		// // The first time, just check if there are any declarations. If there
		// // are, create newScope as usual. Otherwise, let newScope = scope.
		// for (int i = 0; i < statementNode.numChildren(); i++) {
		// BlockItemNode node = statementNode.getSequenceChild(i);
		//
		// if (node instanceof VariableDeclarationNode
		// || node instanceof FunctionDeclarationNode) {
		// newScopeNeeded = true;
		// break;
		// }
		// if (node instanceof LabeledStatementNode) {
		// StatementNode labeledStatementNode = ((LabeledStatementNode) node)
		// .getStatement();
		// if (labeledStatementNode instanceof VariableDeclarationNode) {
		// newScopeNeeded = true;
		// break;
		// }
		// }
		// }
		// if (!newScopeNeeded) {
		// newScopeNeeded = needsNewScope(statementNode.parent().getScope(),
		// statementNode);
		// }
		if (newScopeNeeded)
			newScope = modelFactory.scope(modelFactory.sourceOf(statementNode),
					scope, new LinkedHashSet<Variable>(),
					functionInfo.function());
		else
			newScope = scope;
		location = modelFactory.location(
				modelFactory.sourceOfBeginning(statementNode), newScope);
		for (int i = 0; i < statementNode.numChildren(); i++) {
			BlockItemNode node = statementNode.getSequenceChild(i);
			Fragment fragment = translateASTNode(node, newScope,
					usedLocation ? null : location);

			if (fragment != null) {
				usedLocation = true;
				result = result.combineWith(fragment);
			}
		}
		return result;
	}

	/**
	 * Checks if an AST node contains any $here node in a certain scope.
	 * 
	 * In order to eliminate unnecessary scopes, do this loop twice. The first
	 * time, just check if there are any declarations. If there are, create
	 * newScope as usual. Otherwise, let newScope = scope.
	 * 
	 * @param scope
	 *            The scope to be checked.
	 * @param compound
	 *            The AST node to be checked.
	 * @return True iff a $here node exists in the AST node and is in the given
	 *         scope.
	 */
	private boolean needsNewScope(CompoundStatementNode compound) {
		int numChildren = compound.numChildren();

		for (int i = 0; i < numChildren; i++) {
			BlockItemNode blockItem = compound.getSequenceChild(i);

			if (blockItem instanceof VariableDeclarationNode
					|| blockItem instanceof FunctionDeclarationNode) {
				return true;
			}
			if (blockItem instanceof CompoundStatementNode)
				continue;
			if (blockItem instanceof LabeledStatementNode) {
				StatementNode labeledStatementNode = ((LabeledStatementNode) blockItem)
						.getStatement();
				if (labeledStatementNode instanceof VariableDeclarationNode) {
					return true;
				}
			}
			if (hasHereNodeWork(blockItem))
				return true;
		}
		return false;
	}

	// private boolean containsHereNodeInFirstPrimitiveStatement(
	// StatementNode statementNode) {
	// if (statementNode instanceof CompoundStatementNode) {
	// CompoundStatementNode compound = (CompoundStatementNode) statementNode;
	// int numChildren = compound.numChildren();
	// StatementNode first = null;
	//
	// for (int i = 0; i < numChildren; i++) {
	// BlockItemNode child = compound.getSequenceChild(i);
	//
	// if (child == null)
	// continue;
	// if (child instanceof VariableDeclarationNode)
	// return false;
	// if (!(child instanceof StatementNode))
	// continue;
	// return containsHereNodeInFirstPrimitiveStatement((StatementNode) child);
	// }
	// return false;
	// } else if(statementNode instanceof IfNode) {
	// IfNode if
	// }
	// }

	private boolean hasHereNodeWork(ASTNode node) {
		if (isHereNode(node)) {
			return true;
		}

		int numChildren = node.numChildren();

		for (int i = 0; i < numChildren; i++) {
			ASTNode child = node.child(i);

			if (child == null)
				continue;
			if (child instanceof CompoundStatementNode)
				continue;
			if (hasHereNodeWork(child))
				return true;
		}
		return false;
	}

	private boolean isHereNode(ASTNode node) {
		if (node instanceof HereOrRootNode) {
			return ((HereOrRootNode) node).isHereNode();
		}
		return false;
	}

	/**
	 * Takes an expression statement and converts it to a fragment of that
	 * statement. For spawn, assign, function call, increment and decrement,
	 * they are translated into spawn or call statement, and assignment,
	 * respectively. Any other expressions are translated into a noop statement,
	 * and the original expression becomes one field of the noop statement,
	 * which will be evaluated when executing the noop, and the result of
	 * evaluating the expression is discarded but any side effect error during
	 * evaluation will be reported, like array index out of bound, division by
	 * zero, etc.
	 * 
	 * @param scope
	 *            The scope containing this statement.
	 * @param expressionNode
	 *            The expression node to be translated.
	 * @return the fragment representing the expression node.
	 */
	private Fragment translateExpressionStatementNode(Scope scope,
			ExpressionNode expressionNode) {
		Fragment result;
		Location location = modelFactory.location(
				modelFactory.sourceOfBeginning(expressionNode), scope);

		switch (expressionNode.expressionKind()) {
		// case CAST: {
		// CastNode castNode = (CastNode) expressionNode;
		// CIVLType castType = translateABCType(
		// modelFactory.sourceOf(castNode.getCastType()), scope,
		// castNode.getCastType().getType());
		//
		// if (castType.isVoidType()) {
		// Statement noopStatement = modelFactory.noopStatement(
		// modelFactory.sourceOf(castNode), location);
		//
		// result = new CommonFragment(noopStatement);
		// } else
		// throw new CIVLUnimplementedFeatureException(
		// "expression statement of a cast expression with the cast type "
		// + castType,
		// modelFactory.sourceOf(expressionNode));
		// break;
		// }
		case OPERATOR: {
			OperatorNode operatorNode = (OperatorNode) expressionNode;

			switch (operatorNode.getOperator()) {
			case ASSIGN:
				result = translateAssignNode(scope, operatorNode);
				break;
			case COMMA: {
				int number = operatorNode.getNumberOfArguments();
				result = new CommonFragment();

				for (int i = 0; i < number; i++) {
					ExpressionNode argument = operatorNode.getArgument(i);
					Fragment current = this.translateExpressionStatementNode(
							scope, argument);

					result = result.combineWith(current);
				}
				break;
			}
			case POSTINCREMENT:
			case PREINCREMENT:
			case POSTDECREMENT:
			case PREDECREMENT:
				throw new CIVLInternalException("Side-effect not removed: ",
						modelFactory.sourceOf(operatorNode));
			default: {// since side-effects have been removed,
						// the only expressions remaining with side-effects
						// are assignments. all others are equivalent to no-op
				Expression expression = this.translateExpressionNode(
						expressionNode, scope, true);
				Statement noopStatement = modelFactory.noopStatement(
						modelFactory.sourceOf(operatorNode), location,
						expression);

				result = new CommonFragment(noopStatement);
			}
			}
			break;
		}
		case SPAWN:
			result = translateSpawnNode(scope, (SpawnNode) expressionNode);
			break;
		case FUNCTION_CALL:
			result = translateFunctionCallNode(scope,
					(FunctionCallNode) expressionNode,
					modelFactory.sourceOf(expressionNode));
			break;
		case CONSTANT:
			// case IDENTIFIER_EXPRESSION: {
			// Statement noopStatement = modelFactory.noopStatement(
			// modelFactory.sourceOf(expressionNode), location, null);
			//
			// result = new CommonFragment(noopStatement);
			// }
			// break;
		default: {
			Expression expression = this.translateExpressionNode(
					expressionNode, scope, true);
			Statement noopStatement = modelFactory
					.noopStatement(modelFactory.sourceOf(expressionNode),
							location, expression);

			result = new CommonFragment(noopStatement);
			// throw new CIVLUnimplementedFeatureException(
			// "expression statement of this kind "
			// + expressionNode.expressionKind(),
			// modelFactory.sourceOf(expressionNode));
		}
		}
		return result;
	}

	/**
	 * Translate a for loop node into a fragment. A for loop has the form
	 * <code> for (init; cond; inc) stmt </code>, where <code>init</code> is a
	 * {@link ForLoopInitializerNode} which either is a variable declaration
	 * list or an expression (the expression could be a comma expression, like
	 * <code>int i = 0, j = 0</code>), <code>cond</code> is a boolean expression
	 * which is side-effect-free, and <code>inc</code> is an expression (also
	 * could be a comma expression, like <code>i=i+1,j=j+1</code>). All side
	 * effects except assignments should have been removed already.
	 * 
	 * @param scope
	 *            The scope
	 * @param forLoopNode
	 *            The for loop node
	 * @return the fragment representing the for loop
	 */
	private Fragment translateForLoopNode(Scope scope, ForLoopNode forLoopNode) {
		ForLoopInitializerNode initNode = forLoopNode.getInitializer();
		Fragment initFragment = new CommonFragment();
		Fragment result;

		// If the initNode does not have a declaration, don't create a new
		// scope.
		if (initNode != null) {
			Triple<Scope, Fragment, List<Variable>> initData = translateForLoopInitializerNode(
					scope, initNode);

			scope = initData.first;
			initFragment = initData.second;
		}
		result = composeLoopFragment(scope, forLoopNode.getCondition(),
				forLoopNode.getBody(), forLoopNode.getIncrementer(), false);
		result = initFragment.combineWith(result);
		return result;
	}

	private Triple<Scope, Fragment, List<Variable>> translateForLoopInitializerNode(
			Scope scope, ForLoopInitializerNode initNode) {
		Location location;
		Fragment initFragment = new CommonFragment();
		Scope newScope = scope;
		List<Variable> variables = new ArrayList<>();

		switch (initNode.nodeKind()) {
		case EXPRESSION:
			ExpressionNode initExpression = (ExpressionNode) initNode;

			location = modelFactory.location(
					modelFactory.sourceOfBeginning(initNode), newScope);
			initFragment = translateExpressionStatementNode(newScope,
					initExpression);
			break;
		case DECLARATION_LIST:
			newScope = modelFactory.scope(modelFactory.sourceOf(initNode),
					newScope, new LinkedHashSet<Variable>(),
					functionInfo.function());
			for (int i = 0; i < ((DeclarationListNode) initNode).numChildren(); i++) {
				VariableDeclarationNode declaration = ((DeclarationListNode) initNode)
						.getSequenceChild(i);

				if (declaration == null)
					continue;

				Variable variable = translateVariableDeclarationNode(
						declaration, newScope);
				Fragment fragment;

				variables.add(variable);
				location = modelFactory.location(
						modelFactory.sourceOfBeginning(initNode), newScope);
				fragment = translateVariableInitializationNode(declaration,
						variable, location, newScope);
				initFragment = initFragment.combineWith(fragment);
			}
			break;
		default:
			throw new CIVLInternalException(
					"A for loop initializer must be an expression or a declaration list.",
					modelFactory.sourceOf(initNode));
		}
		return new Triple<>(newScope, initFragment, variables);
	}

	/**
	 * Translate a function call node into a fragment containing the call
	 * statement.
	 * 
	 * @param scope
	 *            The scope
	 * @param functionCallNode
	 *            The function call node
	 * @return the fragment containing the function call statement
	 */
	private Statement translateFunctionCall(Scope scope, LHSExpression lhs,
			FunctionCallNode functionCallNode, boolean isCall, CIVLSource source) {
		// CIVLSource source =
		// modelFactory.sourceOfBeginning(functionCallNode);TODO:Changed
		ArrayList<Expression> arguments = new ArrayList<Expression>();
		Location location;
		CIVLFunction civlFunction = null;
		Function callee;
		ExpressionNode functionExpression = functionCallNode.getFunction();
		CallOrSpawnStatement callStmt;

		if (functionExpression instanceof IdentifierExpressionNode) {
			Entity entity = ((IdentifierExpressionNode) functionExpression)
					.getIdentifier().getEntity();

			if (entity.getEntityKind() == EntityKind.FUNCTION) {
				callee = (Function) entity;
				civlFunction = modelBuilder.functionMap.get(callee);
			}
		}
		for (int i = 0; i < functionCallNode.getNumberOfArguments(); i++) {
			Expression actual = translateExpressionNode(
					functionCallNode.getArgument(i), scope, true);

			actual = arrayToPointer(actual);
			arguments.add(actual);
		}
		location = modelFactory.location(
				modelFactory.sourceOfBeginning(functionCallNode), scope);
		if (civlFunction != null) {
			if (civlFunction.isAbstractFunction()) {
				Expression abstractFunctionCall = modelFactory
						.abstractFunctionCallExpression(
								modelFactory.sourceOf(functionCallNode),
								(AbstractFunction) civlFunction, arguments);

				return modelFactory.assignStatement(source, location, lhs,
						abstractFunctionCall, false);
			}
			callStmt = callOrSpawnStatement(scope, location, functionCallNode,
					lhs, arguments, isCall, source);
			callStmt.setFunction(modelFactory.functionIdentifierExpression(
					civlFunction.getSource(), civlFunction));
			if (callStmt.isSystemCall())
				callStmt.setGuard(modelFactory.systemGuardExpression(callStmt));
			return callStmt;
		} else
			// call on a function pointer
			return callOrSpawnStatement(scope, location, functionCallNode, lhs,
					arguments, isCall, source);

	}

	/**
	 * Translate a function call node into a fragment containing the call
	 * statement
	 * 
	 * @param scope
	 *            The scope
	 * @param functionCallNode
	 *            The function call node
	 * @return the fragment containing the function call statement
	 */
	private Fragment translateFunctionCallNode(Scope scope,
			FunctionCallNode functionCallNode, CIVLSource source) {
		Statement functionCall = translateFunctionCall(scope, null,
				functionCallNode, true, source);

		return new CommonFragment(functionCall);
	}

	/**
	 * Processes a function declaration node (whether or not node is also a
	 * definition node).
	 * 
	 * Let F be the ABC Function Entity corresponding to this function
	 * declaration.
	 * 
	 * First, see if there is already a CIVL Function CF corresponding to F. If
	 * not, create one and add it to the model and map(s). This may be an
	 * ordinary or a system function. (It is a system function if F does not
	 * have any definition.)
	 * 
	 * Process the contract (if any) and add it to whatever is already in the
	 * contract fields of CF.
	 * 
	 * If F is a function definition, add to lists of unprocessed function
	 * definitions: unprocessedFunctions.add(node); containingScopes.put(node,
	 * scope);. Function bodies will be processed at a later pass.
	 * 
	 * @param node
	 *            any ABC function declaration node
	 * @param scope
	 *            the scope in which the function declaration occurs
	 */
	private void translateFunctionDeclarationNode(FunctionDeclarationNode node,
			Scope scope, ArrayList<Variable> scopedParameters) {
		Function entity = node.getEntity();
		SequenceNode<ContractNode> contract = node.getContract();
		CIVLFunction result;

		if (entity == null)
			throw new CIVLInternalException("Unresolved function declaration",
					modelFactory.sourceOf(node));
		// ignore pure function declarations for functions that have its
		// corresponding definition node.
		if ((entity.getDefinition() != null)
				&& (!(node instanceof FunctionDefinitionNode))) {
			// Since function definition hasn't be translated, find out the
			// definition node, translate it.
			FunctionDefinitionNode defNode = entity.getDefinition();

			translateASTNode(defNode, scope, null);
		}
		result = modelBuilder.functionMap.get(entity);
		if (result == null) {
			CIVLSource nodeSource = modelFactory.sourceOf(node);
			String functionName = entity.getName();
			CIVLSource identifierSource = modelFactory.sourceOf(node
					.getIdentifier());
			Identifier functionIdentifier = modelFactory.identifier(
					identifierSource, functionName);
			ArrayList<Variable> parameters = new ArrayList<Variable>();
			// type should come from entity, not this type node.
			// if it has a definition node, should probably use that one.
			FunctionType functionType = entity.getType();
			FunctionTypeNode functionTypeNode = (FunctionTypeNode) node
					.getTypeNode();
			CIVLType returnType = translateABCType(
					modelFactory.sourceOf(functionTypeNode.getReturnType()),
					scope, functionType.getReturnType());
			SequenceNode<VariableDeclarationNode> abcParameters = functionTypeNode
					.getParameters();
			int numParameters = abcParameters.numChildren();

			if (scopedParameters != null) {
				parameters.addAll(0, scopedParameters);
			}
			for (int i = 0; i < numParameters; i++) {
				VariableDeclarationNode decl = abcParameters
						.getSequenceChild(i);

				// Don't process void types. Should only happen in the prototype
				// of a function with no parameters.
				if (decl.getTypeNode().kind() == TypeNodeKind.VOID)
					continue;
				else {
					CIVLType type = translateABCType(
							modelFactory.sourceOf(decl), scope,
							functionType.getParameterType(i));
					CIVLSource source = modelFactory.sourceOf(decl);
					String varName = decl.getName() == null ? "_arg" + i : decl
							.getName();
					Identifier variableName = modelFactory.identifier(source,
							varName);
					Variable parameter = modelFactory.variable(source, type,
							variableName, parameters.size() + 1);

					if (decl.getTypeNode().isConstQualified())
						parameter.setConst(true);
					parameters.add(parameter);
				}
			}
			if (entity.getDefinition() == null) { // abstract or system function
				if (node instanceof AbstractFunctionDefinitionNode) {
					if (parameters.isEmpty())
						throw new CIVLSyntaxException(
								"$abstract functions must have at least one input.\n"
										+ "An abstract function with 0 inputs is a constant.\n"
										+ "It can be declared as an unconstrained input variable instead, e.g.\n"
										+ "$input int N;", node.getSource());
					result = modelFactory.abstractFunction(nodeSource,
							functionIdentifier, parameters, returnType, scope,
							((AbstractFunctionDefinitionNode) node)
									.continuity());
				} else {
					Source declSource = node.getIdentifier().getSource();
					CivlcToken token = declSource.getFirstToken();
					File file = token.getSourceFile().getFile();
					// fileName will be something like "stdlib.h" or "civlc.h"
					String fileName = file.getName();
					String libName;

					switch (functionIdentifier.name()) {
					case "$assert":
					case "$assume":
					case "$defined":
						libName = "civlc";
						break;
					case "$assert_equals":
					case "$equals":
						libName = "pointer";
						break;
					default:
						if (!fileName.contains("."))
							throw new CIVLInternalException(
									"Malformed file name " + fileName
											+ " containing system function "
											+ functionName, nodeSource);
						libName = fileNameWithoutExtension(fileName);
					}
					// if (functionIdentifier.name().equals("$assert"))
					// libName = "civlc";
					// else if (functionIdentifier.name().equals("$equals"))
					// libName = "pointer";
					// else
					// libName = fileNameWithoutExtension(fileName);
					result = modelFactory.systemFunction(nodeSource,
							functionIdentifier, parameters, returnType, scope,
							libName);
					scope.addFunction(result);
				}
			} else { // regular function
				result = modelFactory.function(nodeSource, functionIdentifier,
						parameters, returnType, scope, null);
				scope.addFunction(result);
				modelBuilder.unprocessedFunctions.add(entity.getDefinition());
			}
			modelBuilder.functionMap.put(entity, result);
		}
		if (contract != null) {
			ContractTranslator contractTranslator = new ContractTranslator(
					modelBuilder, modelFactory, typeFactory, result);
			List<ContractClauseExpression> contracts = new LinkedList<>();

			for (int i = 0; i < contract.numChildren(); i++) {
				ContractNode contractNode = contract.getSequenceChild(i);

				contracts.add(contractTranslator
						.translateContractNode(contractNode));
			}
			result = ContractTranslator.mergeContracts(contracts, typeFactory,
					modelFactory, result);
		}
	}

	/**
	 * callWaitAll = modelFactory.callOrSpawnStatement(parForEndSource,
	 * location, true, modelFactory.waitallFunctionPointer(),
	 * Arrays.asList(this.arrayToPointer(parProcs), domSizeVar), null);
	 * */
	private Statement elaborateDomainCall(Scope scope, Expression domain) {
		CIVLSource source = domain.getSource();
		Location location = modelFactory.location(source, scope);
		CallOrSpawnStatement call = this.modelFactory.callOrSpawnStatement(
				source, location, true, modelFactory.elaborateDomainPointer(),
				Arrays.asList(domain), null);

		// this.modelBuilder.elaborateDomainCalls.add(call);
		return call;
	}

	/**
	 * Translate goto statement, since the labeled location might not have been
	 * processed, record the no-op statement and the label to be complete later
	 * 
	 * @param scope
	 *            The scope
	 * @param gotoNode
	 *            The goto node
	 * @return The fragment of the goto statement
	 */
	private Fragment translateGotoNode(Scope scope, GotoNode gotoNode) {
		OrdinaryLabelNode label = ((Label) gotoNode.getLabel().getEntity())
				.getDefinition();
		Location location = modelFactory.location(
				modelFactory.sourceOfBeginning(gotoNode), scope);
		Statement noop = modelFactory.gotoBranchStatement(
				modelFactory.sourceOf(gotoNode), location, label.getName());

		// At this point, the target of the goto may or may not have been
		// encountered. We store the goto in a map from statements to labels.
		// When labeled statements are encountered, we store a map from the
		// label to the corresponding location. When functionInfo.complete() is
		// called, it will get the label for each goto noop from the map and set
		// the target to the corresponding location.
		functionInfo.putToGotoStatement(noop, label);
		return new CommonFragment(noop);
	}

	/**
	 * Translate an IfNode (i.e., an if-else statement) into a fragment.
	 * 
	 * @param scope
	 *            The scope of the start location of the resulting fragment.
	 * @param ifNode
	 *            The if node to be translated.
	 * @return The fragment of the if-else statements.
	 */
	private Fragment translateIfNode(Scope scope, IfNode ifNode) {
		ExpressionNode conditionNode = ifNode.getCondition();
		Expression expression = translateExpressionNode(conditionNode, scope,
				true);
		Fragment beforeCondition = null, trueBranch, trueBranchBody, falseBranch, falseBranchBody, result;
		Location location = modelFactory.location(
				modelFactory.sourceOfBeginning(ifNode), scope);
		Pair<Fragment, Expression> refineConditional = modelFactory
				.refineConditionalExpression(scope, expression,
						modelFactory.sourceOfBeginning(conditionNode),
						modelFactory.sourceOfEnd(conditionNode));

		beforeCondition = refineConditional.left;
		expression = refineConditional.right;
		try {
			expression = modelFactory.booleanExpression(expression);
		} catch (ModelFactoryException err) {
			throw new CIVLSyntaxException("The condition of the if statement "
					+ expression + " is of " + expression.getExpressionType()
					+ " type which cannot be converted to boolean type.",
					expression.getSource());
		}
		trueBranch = new CommonFragment(modelFactory.ifElseBranchStatement(
				modelFactory.sourceOfBeginning(ifNode.getTrueBranch()),
				location, expression, true));
		falseBranch = new CommonFragment(modelFactory.ifElseBranchStatement(
				modelFactory.sourceOfEnd(ifNode), location, modelFactory
						.unaryExpression(expression.getSource(),
								UNARY_OPERATOR.NOT, expression), false));
		trueBranchBody = translateStatementNode(scope, ifNode.getTrueBranch());
		trueBranch = trueBranch.combineWith(trueBranchBody);
		if (ifNode.getFalseBranch() != null) {
			falseBranchBody = translateStatementNode(scope,
					ifNode.getFalseBranch());
			falseBranch = falseBranch.combineWith(falseBranchBody);
		}
		result = trueBranch.parallelCombineWith(falseBranch);
		if (!beforeCondition.isEmpty()) {
			result = beforeCondition.combineWith(result);
		} else {
			result = this.insertNoopAtBeginning(
					modelFactory.sourceOfBeginning(ifNode), scope, result);
		}
		return result;
	}

	/**
	 * Translate a jump node (i.e., a break or continue statement) into a
	 * fragment.
	 * 
	 * @param scope
	 *            The scope of the source location of jump statement.
	 * @param jumpNode
	 *            The jump node to be translated.
	 * @return The fragment of the break or continue statement
	 */
	private Fragment translateJumpNode(Scope scope, JumpNode jumpNode) {
		Location location = modelFactory.location(
				modelFactory.sourceOfBeginning(jumpNode), scope);
		Statement result = modelFactory.noopStatement(
				modelFactory.sourceOf(jumpNode), location, null);
		JumpKind kind = jumpNode.getKind();

		switch (kind) {
		case BREAK:
			functionInfo.peekBreakStack().add(result);
			break;
		case CONTINUE:
			functionInfo.peekContinueStack().add(result);
			break;
		case GOTO:
			return translateGotoNode(scope, (GotoNode) jumpNode);
		default:// RETURN
			return translateReturnNode(scope, (ReturnNode) jumpNode);
		}
		// if (jumpNode.getKind() == JumpKind.CONTINUE) {
		// functionInfo.peekContinueStack().add(result);
		// } else if (jumpNode.getKind() == JumpKind.BREAK) {
		// functionInfo.peekBreakStack().add(result);
		// } else {
		// throw new CIVLInternalException(
		// "Jump nodes other than BREAK and CONTINUE should be handled seperately.",
		// modelFactory.sourceOf(jumpNode.getSource()));
		// }
		return new CommonFragment(result);
	}

	/**
	 * Translate labeled statements
	 * 
	 * @param scope
	 *            The scope
	 * @param labelStatementNode
	 *            The label statement node
	 * @return The fragment of the label statement
	 */
	private Fragment translateLabelStatementNode(Scope scope,
			LabeledStatementNode labelStatementNode) {
		Fragment result = translateStatementNode(scope,
				labelStatementNode.getStatement());

		functionInfo.putToLabeledLocations(labelStatementNode.getLabel(),
				result.startLocation());
		return result;
	}

	/**
	 * Translate a loop node that is a while node or a do-while node into a
	 * fragment of CIVL statements
	 * 
	 * @param scope
	 *            The scope
	 * @param loopNode
	 *            The while loop node
	 * @return the fragment of the while loop
	 */
	private Fragment translateLoopNode(Scope scope, LoopNode loopNode) {
		Fragment result;

		switch (loopNode.getKind()) {
		case DO_WHILE:
			result = composeLoopFragment(scope, loopNode.getCondition(),
					loopNode.getBody(), null, true);
			break;
		case FOR:
			result = translateForLoopNode(scope, (ForLoopNode) loopNode);
			break;
		default:// case WHILE:
			result = composeLoopFragment(scope, loopNode.getCondition(),
					loopNode.getBody(), null, false);
		}
		if (result.startLocation().getNumOutgoing() > 1)
			result = this.insertNoopAtBeginning(
					modelFactory.sourceOfBeginning(loopNode), scope, result);
		return result;
	}

	/**
	 * Translate a null statement node into a fragment of a no-op statement
	 * 
	 * @param scope
	 *            The scope
	 * @param nullStatementNode
	 *            The null statement node
	 * @return the fragment of the null statement (i.e. no-op statement)
	 */
	private Fragment translateNullStatementNode(Scope scope,
			NullStatementNode nullStatementNode) {
		Location location = modelFactory.location(
				modelFactory.sourceOfBeginning(nullStatementNode), scope);

		return new CommonFragment(modelFactory.noopStatement(
				modelFactory.sourceOf(nullStatementNode), location, null));
	}

	/**
	 * Translate return statements
	 * 
	 * @param scope
	 *            The scope
	 * @param returnNode
	 *            The return node
	 * @return The fragment of the return statement
	 */
	private Fragment translateReturnNode(Scope scope, ReturnNode returnNode) {
		Location location;
		Expression expression;
		CIVLFunction function = this.functionInfo.function();
		Fragment returnFragment, atomicReleaseFragment = new CommonFragment();

		if (returnNode.getExpression() != null) {
			expression = translateExpressionNode(returnNode.getExpression(),
					scope, true);
			if (function.returnType().isBoolType()) {
				try {
					expression = modelFactory.booleanExpression(expression);
				} catch (ModelFactoryException err) {
					throw new CIVLSyntaxException(
							"The return type of the function "
									+ function.name().name()
									+ " is boolean, but the returned expression "
									+ expression
									+ " is of "
									+ expression.getExpressionType()
									+ " type which cannot be converted to boolean type.",
							expression.getSource());
				}
			}
		} else
			expression = null;
		if (this.atomCount > 0) {
			Statement leaveAtom;

			for (int i = 0; i < this.atomCount; i++) {
				location = modelFactory.location(
						modelFactory.sourceOfBeginning(returnNode), scope);
				location.setLeaveAtomic(true);
				leaveAtom = new CommonAtomBranchStatement(location.getSource(),
						location, modelFactory.trueExpression(location
								.getSource()), false);
				atomicReleaseFragment.addNewStatement(leaveAtom);
			}
		}
		if (this.atomicCount > 0) {
			Statement leaveAtomic;

			for (int i = 0; i < this.atomicCount; i++) {
				location = modelFactory.location(
						modelFactory.sourceOfBeginning(returnNode), scope);
				location.setLeaveAtomic(false);
				leaveAtomic = new CommonAtomicLockAssignStatement(
						location.getSource(), modelFactory
								.atomicLockVariableExpression()
								.expressionScope(), modelFactory
								.atomicLockVariableExpression()
								.expressionScope(), location,
						modelFactory.trueExpression(location.getSource()),
						false, modelFactory.atomicLockVariableExpression(),
						new CommonUndefinedProcessExpression(modelFactory
								.systemSource(), typeFactory.processType(),
								modelFactory.undefinedValue(typeFactory
										.processSymbolicType())));
				atomicReleaseFragment.addNewStatement(leaveAtomic);
			}
		}
		location = modelFactory.location(
				modelFactory.sourceOfBeginning(returnNode), scope);
		returnFragment = modelFactory.returnFragment(
				modelFactory.sourceOf(returnNode), location, expression,
				function);
		return atomicReleaseFragment.combineWith(returnFragment);
	}

	/**
	 * Translates a ResultNode as an new variable, and adds it into a
	 * corresponding scope. The $result expression can only be translated by
	 * {@link ContractTranslator}.
	 * 
	 * @param resultNode
	 *            The {@link ResultNode} appears in a contract clause
	 * @param scope
	 *            The scope of the contract clause, same as the scope of
	 *            function arguments
	 * @return
	 */
	protected Expression translateResultNode(ResultNode resultNode, Scope scope) {
		throw new CIVLSyntaxException(
				"$result expression used in a non-contract environment.");
	}

	/**
	 * Translate a spawn node into a fragment containing the spawn statement
	 * 
	 * @param scope
	 *            The scope in which this statement occurs. Must be non-null.
	 * @param spawnNode
	 *            The ABC representation of the spawn, which will be translated
	 *            to yield a new {@link Fragment}. Must be non-null.
	 * @return The fragment of the spawn statement
	 */
	private Fragment translateSpawnNode(Scope scope, SpawnNode spawnNode) {
		return new CommonFragment(translateFunctionCall(scope, null,
				spawnNode.getCall(), false, modelFactory.sourceOf(spawnNode)));
	}

	/**
	 * Translate switch block into a fragment
	 * 
	 * @param scope
	 *            The scope
	 * @param switchNode
	 *            The switch node
	 * @return The fragment of the switch statements
	 */
	private Fragment translateSwitchNode(Scope scope, SwitchNode switchNode) {
		Fragment result = new CommonFragment();
		Iterator<LabeledStatementNode> cases = switchNode.getCases();
		Expression condition = translateExpressionNode(
				switchNode.getCondition(), scope, true);
		// Collect case guards to determine guard for default case.
		Expression combinedCaseGuards = null;
		Fragment bodyGoto;
		Statement defaultExit = null;
		Set<Statement> breaks;
		Location location = modelFactory.location(modelFactory.sourceOfSpan(
				modelFactory.sourceOfBeginning(switchNode),
				modelFactory.sourceOfBeginning(switchNode.child(1))), scope);

		functionInfo.addBreakSet(new LinkedHashSet<Statement>());
		// All caseGoto and defaultGoto statements will be updated with the
		// correct target location in the method
		// functionInfo.completeFunction(). So it is not a problem to have it
		// wrong here, because it will finally get corrected.
		while (cases.hasNext()) {
			LabeledStatementNode caseStatement = cases.next();
			SwitchLabelNode label;
			Expression caseGuard;
			Fragment caseGoto;
			Expression labelExpression;

			assert caseStatement.getLabel() instanceof SwitchLabelNode;
			label = (SwitchLabelNode) caseStatement.getLabel();
			labelExpression = translateExpressionNode(label.getExpression(),
					scope, true);
			caseGuard = modelFactory.binaryExpression(
					modelFactory.sourceOf(label.getExpression()),
					BINARY_OPERATOR.EQUAL, condition, labelExpression);
			if (combinedCaseGuards == null) {
				combinedCaseGuards = caseGuard;
			} else {
				combinedCaseGuards = modelFactory.binaryExpression(modelFactory
						.sourceOfSpan(caseGuard.getSource(),
								combinedCaseGuards.getSource()),
						BINARY_OPERATOR.OR, caseGuard, combinedCaseGuards);
			}
			caseGoto = new CommonFragment(modelFactory.switchBranchStatement(
					modelFactory.sourceOf(caseStatement), location, caseGuard,
					labelExpression));
			result = result.parallelCombineWith(caseGoto);
			for (Statement stmt : caseGoto.finalStatements())
				functionInfo.putToGotoStatement(stmt, label);
		}
		if (switchNode.getDefaultCase() != null) {
			LabelNode label = switchNode.getDefaultCase().getLabel();
			Fragment defaultGoto = new CommonFragment(
					modelFactory.switchBranchStatement(modelFactory
							.sourceOf(switchNode.getDefaultCase()), location,
							modelFactory.unaryExpression(modelFactory
									.sourceOfBeginning(switchNode
											.getDefaultCase()),
									UNARY_OPERATOR.NOT, combinedCaseGuards)));

			result = result.parallelCombineWith(defaultGoto);
			for (Statement stmt : defaultGoto.finalStatements())
				functionInfo.putToGotoStatement(stmt, label);
		} else {
			defaultExit = modelFactory.noopStatementWtGuard(modelFactory
					.sourceOfBeginning(switchNode), location, modelFactory
					.unaryExpression(
							modelFactory.sourceOfBeginning(switchNode),
							UNARY_OPERATOR.NOT, combinedCaseGuards));
		}
		bodyGoto = translateStatementNode(scope, switchNode.getBody());
		// Although it is not correct to have caseGotos and defaultGoto to go to
		// the start location of the switch body, we have to do it here for the
		// following reason: 1. the fragment before the switch block need to set
		// its last statement to go to the start location of this switch
		// fragment; 2. the fragment after the switch block needs to have its
		// start location set to be the target of all last statements of this
		// switch body. We can't return purely caseGotos or bodyGoto without
		// combining them as one fragment. Moreover, it is not
		// a problem to have them wrong here, because they will finally get
		// corrected when calling functionInfo.completeFunction().
		result = result.combineWith(bodyGoto);
		breaks = functionInfo.popBreakStack();
		if (breaks.size() > 0) {
			for (Statement s : breaks) {
				result.addFinalStatement(s);
			}
		}
		if (defaultExit != null)
			result.addFinalStatement(defaultExit);
		return this.insertNoopAtBeginning(
				modelFactory.sourceOfBeginning(switchNode), scope, result);
	}

	/**
	 * Translates a variable declaration node. If the given sourceLocation is
	 * non-null, it is used as the source location for the new statement(s).
	 * Otherwise a new location is generated and used. This method may return
	 * null if no statements are generated as a result of processing the
	 * declaration.
	 * 
	 * @param sourceLocation
	 *            location to use as origin of new statements or null
	 * @param scope
	 *            CIVL scope in which this declaration appears
	 * @param node
	 *            the ABC variable declaration node to translate
	 * @return the pair consisting of the (new or given) start location of the
	 *         generated fragment and the last statement in the sequence of
	 *         statements generated by translating this declaration node, or
	 *         null if no statements are generated
	 * @throws CommandLineException
	 *             if an initializer for an input variable specified on the
	 *             command line does not have a type compatible with the
	 *             variable
	 */
	private Fragment translateVariableDeclarationNode(Location sourceLocation,
			Scope scope, VariableDeclarationNode node)
			throws CommandLineException {
		Variable variable = translateVariableDeclarationNode(node, scope);

		if (variable == null)
			return new CommonFragment();

		CIVLType type = variable.type();
		Fragment result = null, initialization = null;
		IdentifierNode identifier = node.getIdentifier();
		CIVLSource source = modelFactory.sourceOf(node);
		boolean initializerTranslated = false;

		if (sourceLocation == null)
			sourceLocation = modelFactory.location(
					modelFactory.sourceOfBeginning(node), scope);
		result = new CommonFragment(
				modelFactory.noopStatementForVariableDeclaration(source,
						sourceLocation));
		if (variable.isInput() || variable.isStatic()
				|| type instanceof CIVLArrayType
				|| type instanceof CIVLStructOrUnionType || type.isHeapType()) {
			Expression rhs = null;

			if (variable.isInput() && modelBuilder.inputInitMap != null) {
				String name = variable.name().name();
				Object value = modelBuilder.inputInitMap.get(name);

				if (value != null) {
					rhs = constant(variable, value);
					modelBuilder.initializedInputs.add(name);
				}
			}
			if (rhs == null && node.getInitializer() == null)
				rhs = modelFactory.initialValueExpression(source, variable);
			if (sourceLocation == null)
				sourceLocation = modelFactory.location(
						modelFactory.sourceOfBeginning(node), scope);
			if (rhs != null) {
				Location location = modelFactory.location(
						modelFactory.sourceOfEnd(node), scope);

				initializerTranslated = true;
				result = result.combineWith(new CommonFragment(modelFactory
						.assignStatement(source, location, modelFactory
								.variableExpression(
										modelFactory.sourceOf(identifier),
										variable), rhs, true)));
			}
		}
		// for input variables, only use the initialization if there
		// was no command line specification of the input value:
		if (!initializerTranslated || !variable.isInput()) {
			initialization = translateVariableInitializationNode(node,
					variable, null, scope);
			result = result.combineWith(initialization);
		}
		return result;
	}

	/**
	 * Processes a variable declaration. Adds the new variable to the given
	 * scope.
	 * 
	 * @param scope
	 *            the Model scope in which the variable declaration occurs
	 * @param node
	 *            the AST variable declaration node.
	 * @return The variable
	 */
	private Variable translateVariableDeclarationNode(
			VariableDeclarationNode node, Scope scope) {
		edu.udel.cis.vsl.abc.ast.entity.IF.Variable varEntity = node
				.getEntity();
		// node.prettyPrint(System.out);
		// System.out.println();
		if(varEntity.getDefinition()==null)
			throw new CIVLSyntaxException(
					"Can't find the definition for variable "
							+ node.getName(), node.getSource());
		if (!varEntity.getDefinition().equals(node))
			return null;
		
		TypeNode typeNode = node.getTypeNode();
		CIVLType type = translateABCType(modelFactory.sourceOf(typeNode),
				scope, typeNode.getType());
		CIVLSource source = modelFactory.sourceOf(node.getIdentifier());
		Identifier name = modelFactory.identifier(source, node.getName());
		int vid = scope.numVariables();
		Variable variable = modelFactory.variable(source, type, name, vid);

		if (typeNode.isConstQualified())
			variable.setConst(true);
		scope.addVariable(variable);
		if (node.getTypeNode().isInputQualified()) {
			variable.setIsInput(true);
			modelFactory.addInputVariable(variable);
			assert variable.scope().id() == 0;
		}
		if (node.getTypeNode().isOutputQualified()) {
			variable.setIsOutput(true);
		}
		if (node.hasStaticStorage()
				|| (node.getInitializer() == null && scope.id() == 0)) {
			variable.setStatic(true);
		}
		return variable;
	}

	/**
	 * Translate the initializer node of a variable declaration node (if it has
	 * one) into a fragment of an assign statement
	 * 
	 * @param node
	 *            The variable declaration node that might contain an
	 *            initializer node
	 * @param variable
	 *            The variable
	 * @param location
	 *            The location
	 * @param scope
	 *            The scope containing this variable declaration node
	 * @return The fragment
	 */
	private Fragment translateVariableInitializationNode(
			VariableDeclarationNode node, Variable variable, Location location,
			Scope scope) {
		Fragment initFragment = null;
		InitializerNode init = node.getInitializer();
		LHSExpression lhs = modelFactory.variableExpression(
				modelFactory.sourceOf(node), variable);

		if (init != null) {
			Statement assignStatement, anonStatement = null;
			Expression rhs;
			CIVLSource initSource = modelFactory.sourceOf(init);

			if (!(init instanceof ExpressionNode)
					&& !(init instanceof CompoundInitializerNode))
				throw new CIVLUnimplementedFeatureException(
						"Non-expression initializer",
						modelFactory.sourceOf(init));
			if (location == null)
				location = modelFactory.location(
						modelFactory.sourceOfBeginning(node), scope);
			if (init instanceof ExpressionNode) {
				if (init instanceof CompoundLiteralNode
						&& variable.type().isPointerType()) {
					rhs = translateExpressionNode((ExpressionNode) init, scope,
							true);

					Variable anonVariable = modelFactory
							.newAnonymousVariableForArrayLiteral(initSource,
									(CIVLArrayType) rhs.getExpressionType());

					anonStatement = modelFactory.assignStatement(initSource,
							modelFactory.location(initSource, scope),
							modelFactory.variableExpression(initSource,
									anonVariable), rhs, true);
					rhs = arrayToPointer(modelFactory.variableExpression(
							initSource, anonVariable));
					assignStatement = modelFactory.assignStatement(
							modelFactory.sourceOf(node), location, lhs, rhs,
							true);
					initFragment = new CommonFragment(assignStatement);
				} else {
					initFragment = this.assignStatement(
							modelFactory.sourceOf(node), lhs,
							(ExpressionNode) init, true, scope);
				}
			} else {
				CIVLType variableType = variable.type();

				rhs = translateCompoundInitializer(
						((CompoundInitializerNode) init), scope, variableType);
				if (variableType.isPointerType()) {
					Variable anonVariable = modelFactory
							.newAnonymousVariableForArrayLiteral(initSource,
									(CIVLArrayType) rhs.getExpressionType());

					anonStatement = modelFactory.assignStatement(initSource,
							modelFactory.location(initSource, scope),
							modelFactory.variableExpression(initSource,
									anonVariable), rhs, true);
					rhs = arrayToPointer(modelFactory.variableExpression(
							initSource, anonVariable));
				}
				assignStatement = modelFactory.assignStatement(
						modelFactory.sourceOf(node), location, lhs, rhs, true);
				initFragment = new CommonFragment(assignStatement);
			}
			// initFragment = new CommonFragment(assignStatement);
			if (anonStatement != null) {
				initFragment = new CommonFragment(anonStatement)
						.combineWith(initFragment);
			}
			if (!modelFactory.anonFragment().isEmpty()) {
				initFragment = modelFactory.anonFragment().combineWith(
						initFragment);
				modelFactory.clearAnonFragment();
			}
			if (modelFactory.hasConditionalExpressions()) {
				initFragment = modelFactory
						.refineConditionalExpressionOfStatement(initFragment
								.startLocation().getOutgoing(0), location);
			}
		}
		return initFragment;
	}

	private Expression translateCompoundLiteralNode(
			CompoundLiteralNode compoundNode, Scope scope) {
		// TODO: check this. Make sure that users don't need to specify the
		// dimension when using compound literal statement for DomainType.
		CIVLType type = translateABCType(
				modelFactory.sourceOf(compoundNode.getTypeNode()), scope,
				compoundNode.getType());

		return translateCompoundInitializer(compoundNode.getInitializerList(),
				scope, type);
	}

	private Expression translateCompoundInitializer(
			CompoundInitializerNode compoundInit, Scope scope, CIVLType type) {
		CIVLSource source = modelFactory.sourceOf(compoundInit);
		int size = compoundInit.numChildren();
		List<Expression> expressions = new ArrayList<>(size);

		if (!type.isDomainType()) {
			return this.translateLiteralObject(source, scope,
					compoundInit.getLiteralObject(), type);
		} else {
			int dimension;

			if (!(type instanceof CIVLCompleteDomainType))
				throw new CIVLSyntaxException(
						"It is illegal to define a $domain literal without the dimension specified.",
						source);
			dimension = ((CIVLCompleteDomainType) type).getDimension();
			assert size == dimension;
		}
		for (int i = 0; i < size; i++)
			expressions.add(translateInitializerNode(compoundInit
					.getSequenceChild(i).getRight(), scope, typeFactory
					.rangeType()));
		return modelFactory.recDomainLiteralExpression(source, expressions,
				type);
	}

	private Expression translateLiteralObject(CIVLSource source, Scope scope,
			LiteralObject literal, CIVLType type) {
		if (literal instanceof ScalarLiteralObject) {
			ScalarLiteralObject scalar = (ScalarLiteralObject) literal;

			return this.translateExpressionNode(scalar.getExpression(), scope,
					true);
		} else {
			CompoundLiteralObject compound = (CompoundLiteralObject) literal;
			int size = compound.size();
			List<Expression> expressions = new ArrayList<>(size);
			List<CIVLType> types = new ArrayList<>(size);
			int myType; // 0: arrayType, 1: struct or union, -1: other
			CIVLType finalType = type;

			if (type.isArrayType() || type.isPointerType()) {
				if (type.isPointerType()) {
					finalType = typeFactory.completeArrayType(
							((CIVLPointerType) type).baseType(), modelFactory
									.integerLiteralExpression(null,
											BigInteger.valueOf(size)));
				}
				for (int i = 0; i < size; i++)
					types.add(((CIVLArrayType) finalType).elementType());
				myType = 0;
			} else if (type.isStructType() || type.isUnionType()) {
				CIVLStructOrUnionType structType = (CIVLStructOrUnionType) type;

				for (int i = 0; i < size; i++) {
					types.add(structType.getField(i).type());
				}
				myType = 1;
			} else
				throw new CIVLSyntaxException("Compound initializer of " + type
						+ " type is invalid.", source);
			for (int i = 0; i < size; i++)
				expressions.add(this.translateLiteralObject(source, scope,
						compound.get(i), types.get(i)));
			if (myType == 0)
				return modelFactory.arrayLiteralExpression(source,
						(CIVLArrayType) finalType, expressions);
			else if (myType == 1)
				return modelFactory.structOrUnionLiteralExpression(source,
						(CIVLStructOrUnionType) finalType, expressions);
			else
				throw new CIVLUnimplementedFeatureException(
						"translating literal object which is of neither array or struct/union type",
						source);
		}

	}

	private Expression translateInitializerNode(InitializerNode initNode,
			Scope scope, CIVLType type) {
		Expression initExpr;

		if (initNode instanceof ExpressionNode)
			initExpr = this.translateExpressionNode((ExpressionNode) initNode,
					scope, true);
		else if (initNode instanceof CompoundInitializerNode) {
			initExpr = this.translateCompoundInitializer(
					(CompoundInitializerNode) initNode, scope, type);
		} else
			throw new CIVLSyntaxException("Invalid initializer node: "
					+ initNode, initNode.getSource());
		return initExpr;
	}

	/**
	 * Translate a when node into a fragment of a when statement
	 * 
	 * @param scope
	 *            The scope
	 * @param whenNode
	 *            The when node
	 * @return the fragment of the when statement
	 */
	private Fragment translateWhenNode(Scope scope, WhenNode whenNode) {
		ExpressionNode whenGuardNode = whenNode.getGuard();
		Expression whenGuard = translateExpressionNode(whenNode.getGuard(),
				scope, true);
		Pair<Fragment, Expression> refineConditional = modelFactory
				.refineConditionalExpression(scope, whenGuard,
						modelFactory.sourceOfBeginning(whenGuardNode),
						modelFactory.sourceOfEnd(whenGuardNode));
		Fragment beforeGuardFragment = refineConditional.left, result;
		Location whenLocation = modelFactory.location(
				modelFactory.sourceOfBeginning(whenNode), scope);

		whenGuard = refineConditional.right;
		try {
			whenGuard = modelFactory.booleanExpression(whenGuard);
		} catch (ModelFactoryException err) {
			throw new CIVLSyntaxException(
					"The condition of the when statement " + whenGuard
							+ " is of " + whenGuard.getExpressionType()
							+ "type which cannot be converted to "
							+ "boolean type.", whenGuard.getSource());
		}
		result = translateStatementNode(scope, whenNode.getBody());
		if (!modelFactory.isTrue(whenGuard)) {
			// Each outgoing statement from the first location in this
			// fragment should have its guard set to the conjunction of guard
			// and that statement's guard.
			result.addGuardToStartLocation(whenGuard, modelFactory);
		}
		result.updateStartLocation(whenLocation);
		if (beforeGuardFragment != null) {
			result = beforeGuardFragment.combineWith(result);
		}
		return result;
	}

	/* *********************************************************************
	 * Translate AST Expression Node into CIVL Expression
	 * *********************************************************************
	 */

	/**
	 * Translate a struct pointer field reference from the CIVL AST to the CIVL
	 * model.
	 * 
	 * @param arrowNode
	 *            The arrow expression.
	 * @param scope
	 *            The (static) scope containing the expression.
	 * @return The model representation of the expression.
	 */
	private Expression translateArrowNode(ArrowNode arrowNode, Scope scope) {
		Expression struct = translateExpressionNode(
				arrowNode.getStructurePointer(), scope, true);
		Expression result = modelFactory.dotExpression(modelFactory
				.sourceOf(arrowNode),
				modelFactory.dereferenceExpression(
						modelFactory.sourceOf(arrowNode.getStructurePointer()),
						struct), getFieldIndex(arrowNode.getFieldName()));

		return result;
	}

	/**
	 * Translate a cast expression from the CIVL AST to the CIVL model.
	 * 
	 * @param castNode
	 *            The cast expression.
	 * @param scope
	 *            The (static) scope containing the expression.
	 * @return The model representation of the expression.
	 */
	private Expression translateCastNode(CastNode castNode, Scope scope) {
		TypeNode typeNode = castNode.getCastType();
		CIVLType castType = translateABCType(modelFactory.sourceOf(typeNode),
				scope, typeNode.getType());
		ExpressionNode argumentNode = castNode.getArgument();
		Expression castExpression, result;
		CIVLSource source = modelFactory.sourceOf(castNode);

		castExpression = translateExpressionNode(argumentNode, scope, true);
		castExpression = arrayToPointer(castExpression);
		result = modelFactory.castExpression(source, castType, castExpression);
		return result;
	}

	/**
	 * Translate a ConstantNode into a CIVL literal expression
	 * 
	 * @param constantNode
	 *            The constant node
	 * 
	 * @return a CIVL literal expression representing the constant node
	 */
	private Expression translateConstantNode(Scope scope,
			ConstantNode constantNode) {
		CIVLSource source = modelFactory.sourceOf(constantNode);
		Type convertedType = constantNode.getConvertedType();
		Expression result;

		switch (convertedType.kind()) {
		case SCOPE:
			HereOrRootNode scopeConstantNode = (HereOrRootNode) constantNode;

			result = modelFactory.hereOrRootExpression(source,
					scopeConstantNode.isRootNode());
			break;
		case PROCESS:
			String procValue = constantNode.getStringRepresentation();

			if (procValue.equals("$self"))
				result = modelFactory.selfExpression(source);
			else
				result = modelFactory.procnullExpression(source);
			break;
		case OTHER_INTEGER:
			if (constantNode instanceof EnumerationConstantNode) {
				BigInteger value = ((IntegerValue) ((EnumerationConstantNode) constantNode)
						.getConstantValue()).getIntegerValue();

				result = modelFactory.integerLiteralExpression(source, value);
			} else {
				Value value = constantNode.getConstantValue();

				if (value instanceof IntegerValue)
					result = modelFactory.integerLiteralExpression(source,
							((IntegerValue) value).getIntegerValue());
				else if (value instanceof RealFloatingValue)
					result = modelFactory.integerLiteralExpression(source,
							((RealFloatingValue) value).getWholePartValue());
				else
					throw new CIVLSyntaxException(
							"Invalid constant for integers", source);
			}
			break;
		case BASIC: {
			switch (((StandardBasicType) convertedType).getBasicTypeKind()) {
			case SHORT:
			case UNSIGNED_SHORT:
			case INT:
			case UNSIGNED:
			case LONG:
			case UNSIGNED_LONG:
			case LONG_LONG:
			case UNSIGNED_LONG_LONG:
				if (constantNode instanceof EnumerationConstantNode) {
					BigInteger value = ((IntegerValue) ((EnumerationConstantNode) constantNode)
							.getConstantValue()).getIntegerValue();

					result = modelFactory.integerLiteralExpression(source,
							value);
				} else {
					Value value = constantNode.getConstantValue();

					if (value instanceof IntegerValue)
						result = modelFactory.integerLiteralExpression(source,
								((IntegerValue) value).getIntegerValue());
					else if (value instanceof RealFloatingValue)
						result = modelFactory
								.integerLiteralExpression(source,
										((RealFloatingValue) value)
												.getWholePartValue());
					else
						throw new CIVLSyntaxException(
								"Invalid constant for integers", source);
				}
				break;
			case FLOAT:
			case DOUBLE:
			case LONG_DOUBLE:
				String doubleString = constantNode.getStringRepresentation();

				if (doubleString.endsWith("l") || doubleString.endsWith("L")
						|| doubleString.endsWith("f")
						|| doubleString.endsWith("F")) {
					doubleString = doubleString.substring(0,
							doubleString.length() - 1);
				}
				result = modelFactory.realLiteralExpression(source,
						BigDecimal.valueOf(Double.parseDouble(doubleString)));

				break;
			case BOOL:
				boolean value;

				if (constantNode instanceof IntegerConstantNode) {
					BigInteger integerValue = ((IntegerConstantNode) constantNode)
							.getConstantValue().getIntegerValue();

					if (integerValue.intValue() == 0) {
						value = false;
					} else {
						value = true;
					}
				} else {
					value = Boolean.parseBoolean(constantNode
							.getStringRepresentation());
				}
				result = modelFactory.booleanLiteralExpression(source, value);
				break;
			case CHAR:
			case UNSIGNED_CHAR:
				Value constValue = constantNode.getConstantValue();
				ConstantKind constKind = constantNode.constantKind();
				char[] charValues;
				BigInteger intValues;

				if (constKind.equals(ConstantKind.CHAR)) {
					try {
						charValues = ((CharacterValue) constValue)
								.getCharacter().getCharacters();
						assert (charValues.length == 1) : constValue
								+ " is not belong to execution characters set\n";
					} catch (ClassCastException e) {
						throw new CIVLInternalException(
								"CHAR Constant value casting failed\n", source);
					}
				} else if (constKind.equals(ConstantKind.INT)) {
					try {
						// TODO: what about signed char which allows assigned by
						// negative int objects ?
						intValues = ((IntegerValue) constValue)
								.getIntegerValue();
						if (intValues.intValue() < 0
								|| intValues.intValue() > 255)
							throw new CIVLUnimplementedFeatureException(
									"Converting integer whose value is larger than UCHAR_MAX or is less than UCHAR_MIN to char type\n");
						charValues = new char[1];
						charValues[0] = (char) intValues.intValue();
					} catch (ClassCastException e) {
						throw new CIVLInternalException(
								"INT Constant value casting failed\n", source);
					}
				} else
					throw new CIVLSyntaxException(source.getSummary() + " to "
							+ convertedType.toString());

				result = modelFactory.charLiteralExpression(source,
						charValues[0]);
				break;
			default:
				throw new CIVLUnimplementedFeatureException("type "
						+ convertedType, source);
			}
			break;
		}
		case ENUMERATION:
			if (constantNode instanceof EnumerationConstantNode) {
				BigInteger value = ((IntegerValue) ((EnumerationConstantNode) constantNode)
						.getConstantValue()).getIntegerValue();

				result = modelFactory.integerLiteralExpression(source, value);
			} else
				result = modelFactory.integerLiteralExpression(source,
						BigInteger.valueOf(Long.parseLong(constantNode
								.getStringRepresentation())));
			break;
		case POINTER:
		case ARRAY:
			boolean isSupportedChar = false;

			if (constantNode.getStringRepresentation().equals("0")) {
				result = modelFactory
						.nullPointerExpression(
								typeFactory.pointerType(typeFactory.voidType()),
								source);
				break;
			} else if (convertedType.kind() == TypeKind.POINTER
					&& constantNode instanceof IntegerConstantNode) {
				result = modelFactory.integerLiteralExpression(source,
						((IntegerConstantNode) constantNode).getConstantValue()
								.getIntegerValue());
				break;
			} else if (constantNode instanceof StringLiteralNode) {
				Type elementType = null;

				if (convertedType.kind() == TypeKind.POINTER) {
					elementType = ((PointerType) convertedType)
							.referencedType();
				} else {// convertedType.kind() == ARRAY
					elementType = ((ArrayType) convertedType).getElementType();
				}
				if (elementType.kind() == TypeKind.QUALIFIED) {
					elementType = ((QualifiedObjectType) elementType)
							.getBaseType();
				}
				if (elementType != null && elementType.kind() == TypeKind.BASIC) {
					if (((StandardBasicType) elementType).getBasicTypeKind() == BasicTypeKind.CHAR)
						isSupportedChar = true;
				}
				// }
				//
				// if(convertedType.kind() == TypeKind.POINTER && ((PointerType)
				// convertedType).referencedType().kind() == TypeKind.BASIC
				// && ((StandardBasicType) ((PointerType) convertedType)
				// .referencedType()).getBasicTypeKind() == BasicTypeKind.CHAR)
				// {
				// isSupportedChar = true;
				// }else if(((ArrayType)convertedType).getElementType().kind()
				// == ){
				//
				// } else if (((PointerType) convertedType).referencedType()
				// .kind() == TypeKind.QUALIFIED
				// && ((QualifiedObjectType) ((PointerType) convertedType)
				// .referencedType()).getBaseType() instanceof
				// StandardBasicType) {
				// StandardBasicType basicType = (StandardBasicType)
				// (((QualifiedObjectType) ((PointerType) convertedType)
				// .referencedType()).getBaseType());
				//
				// if (basicType.getBasicTypeKind() == BasicTypeKind.CHAR)
				// isSupportedChar = true;
				// }
				if (isSupportedChar) {
					StringLiteralNode stringLiteralNode = (StringLiteralNode) constantNode;
					StringLiteral stringValue = stringLiteralNode
							.getConstantValue().getLiteral();
					CIVLArrayType arrayType = typeFactory.completeArrayType(
							typeFactory.charType(), modelFactory
									.integerLiteralExpression(source,
											BigInteger.valueOf(stringValue
													.getNumCharacters())));
					ArrayList<Expression> chars = new ArrayList<>();
					ArrayLiteralExpression stringLiteral;
					VariableExpression anonVariable = modelFactory
							.variableExpression(source, modelFactory
									.newAnonymousVariableForArrayLiteral(
											source, arrayType));
					Statement anonAssign;

					for (int i = 0; i < stringValue.getNumCharacters(); i++) {
						for (char c : stringValue.getCharacter(i)
								.getCharacters()) {
							chars.add(modelFactory.charLiteralExpression(
									source, c));
						}
					}
					stringLiteral = modelFactory.arrayLiteralExpression(source,
							arrayType, chars);
					anonAssign = modelFactory.assignStatement(source,
							modelFactory.location(source, scope), anonVariable,
							stringLiteral, true);
					modelFactory.addAnonStatement(anonAssign);
					// result = arrayToPointer(anonVariable);
					result = anonVariable;
					break;
				}
			}
		default:
			throw new CIVLUnimplementedFeatureException(
					"type " + convertedType, source);
		}
		return result;
	}

	/**
	 * Translate a struct field reference from the CIVL AST to the CIVL model.
	 * 
	 * @param dotNode
	 *            The dot node to be translated.
	 * @param scope
	 *            The (static) scope containing the expression.
	 * @return The model representation of the expression.
	 */
	private Expression translateDotNode(DotNode dotNode, Scope scope) {
		Expression struct = translateExpressionNode(dotNode.getStructure(),
				scope, true);
		Expression result = modelFactory.dotExpression(
				modelFactory.sourceOf(dotNode), struct,
				getFieldIndex(dotNode.getFieldName()));

		return result;
	}

	/**
	 * Translate an ExpressionNode object in the AST into a CIVL Expression
	 * object
	 * 
	 * @param expressionNode
	 *            The expression node
	 * @param scope
	 *            The scope
	 * @param translateConversions
	 *            The translation conversions
	 * @return the CIVL Expression object
	 */
	protected Expression translateExpressionNode(ExpressionNode expressionNode,
			Scope scope, boolean translateConversions) {
		Expression result;

		switch (expressionNode.expressionKind()) {
		case ARROW:
			result = translateArrowNode((ArrowNode) expressionNode, scope);
			break;
		case CAST:
			result = translateCastNode((CastNode) expressionNode, scope);
			break;
		case COMPOUND_LITERAL:
			result = translateCompoundLiteralNode(
					(CompoundLiteralNode) expressionNode, scope);
			break;
		case CONSTANT:
			result = translateConstantNode(scope, (ConstantNode) expressionNode);
			break;
		case DERIVATIVE_EXPRESSION:
			result = translateDerivativeExpressionNode(
					(DerivativeExpressionNode) expressionNode, scope);
			break;
		case DOT:
			result = translateDotNode((DotNode) expressionNode, scope);
			break;
		case FUNCTION_CALL:
			result = translateFunctionCallExpression(
					(FunctionCallNode) expressionNode, scope);
			break;
		case IDENTIFIER_EXPRESSION:
			result = translateIdentifierNode(
					(IdentifierExpressionNode) expressionNode, scope);
			break;
		case OPERATOR:
			result = translateOperatorNode((OperatorNode) expressionNode, scope);
			break;
		case QUANTIFIED_EXPRESSION:
			result = translateQuantifiedExpressionNode(
					(QuantifiedExpressionNode) expressionNode, scope);
			break;
		case REGULAR_RANGE:
			result = translateRegularRangeNode(
					(RegularRangeNode) expressionNode, scope);
			break;
		case SCOPEOF:
			result = translateScopeofNode((ScopeOfNode) expressionNode, scope);
			break;
		// TODO: check this, but this case does not exist, it is handled
		// as a constant expression:
		// case SELF:
		// result = modelFactory.selfExpression(modelFactory
		// .sourceOf(expressionNode));
		// break;
		case SIZEOF:
			result = translateSizeofNode((SizeofNode) expressionNode, scope);
			break;
		case REMOTE_REFERENCE:
			result = translateRemoteReferenceNode(
					(RemoteExpressionNode) expressionNode, scope);
			break;
		case RESULT:
			result = translateResultNode((ResultNode) expressionNode, scope);
			break;
		default:
			throw new CIVLUnimplementedFeatureException("expressions of type "
					+ expressionNode.getClass().getSimpleName(),
					modelFactory.sourceOf(expressionNode));
		}
		if (translateConversions) {
			result = this.applyConversions(scope, expressionNode, result);
		}
		return result;
	}

	/**
	 * Applies conversions associated with the given expression node to the
	 * given expression.
	 * 
	 * Precondition: the given expression is the CIVL representation of the
	 * given expression node before conversions.
	 * 
	 * @param scope
	 * @param expressionNode
	 * @param expression
	 * @return
	 */
	private Expression applyConversions(Scope scope,
			ExpressionNode expressionNode, Expression expression) {
		// apply conversions
		CIVLSource source = expression.getSource();
		int numConversions = expressionNode.getNumConversions();

		for (int i = 0; i < numConversions; i++) {
			Conversion conversion = expressionNode.getConversion(i);
			Type oldType = conversion.getOldType();
			Type newType = conversion.getNewType();
			// Arithmetic, Array, CompatibleStructureOrUnion,
			// Function, Lvalue, NullPointer, PointerBool, VoidPointer
			ConversionKind kind = conversion.conversionKind();

			switch (kind) {
			case ARITHMETIC: {
				CIVLType oldCIVLType = translateABCType(source, scope, oldType);
				CIVLType newCIVLType = translateABCType(source, scope, newType);

				// need equals on Types
				if (oldCIVLType.isIntegerType() && newCIVLType.isIntegerType()
						|| oldCIVLType.isRealType() && newCIVLType.isRealType()) {
					// nothing to do
				} else {
					// Sometimes the conversion might have been done during
					// the translating the expression node, for example,
					// when translating a constant node, so only create a
					// cast expression if necessary.
					if (!expression.getExpressionType().equals(newCIVLType))
						expression = modelFactory.castExpression(source,
								newCIVLType, expression);
				}
				break;
			}
			case ARRAY: {
				if (expressionNode.expressionKind() == ExpressionKind.OPERATOR
						&& ((OperatorNode) expressionNode).getOperator() == Operator.SUBSCRIPT) {
					// we will ignore this one here because we want
					// to keep it as array in subscript expressions
				} else if (expression.expressionKind() == Expression.ExpressionKind.ADDRESS_OF
						|| expression.expressionKind() == Expression.ExpressionKind.ARRAY_LITERAL) {
					// FIXME: Not sure why this needs to be checked...
				} else {
					assert expression instanceof LHSExpression;
					expression = modelFactory.addressOfExpression(source,
							modelFactory.subscriptExpression(source,
									(LHSExpression) expression, modelFactory
											.integerLiteralExpression(source,
													BigInteger.ZERO)));
				}
				break;
			}
			case COMPATIBLE_POINTER:// nothing to do
				break;
			case COMPATIBLE_STRUCT_UNION: {
				// TODO think about how to implement this
				throw new CIVLUnimplementedFeatureException(
						"compatible structure or union conversion", source);
			}
			case FUNCTION:
				break;
			case LVALUE:
				break;
			case MEMORY:
				break;
			case NULL_POINTER: {
				// result is a null pointer to new type
				CIVLType tmpType = translateABCType(source, scope, newType);
				CIVLPointerType newCIVLType = (CIVLPointerType) tmpType;

				expression = modelFactory.nullPointerExpression(newCIVLType,
						source);
				break;
			}
			case POINTER_BOOL: {
				// pointer type to boolean type: p!=NULL
				expression = modelFactory.binaryExpression(source,
						BINARY_OPERATOR.NOT_EQUAL, expression, modelFactory
								.nullPointerExpression(
										(CIVLPointerType) expression
												.getExpressionType(), source));
				break;
			}
			case REG_RANGE_DOMAIN: {
				// $range -> $domain(1)
				expression = modelFactory.recDomainLiteralExpression(
						source,
						Arrays.asList(expression),
						typeFactory.completeDomainType(
								expression.getExpressionType(), 1));
				break;
			}
			case POINTER_INTEGER: {
				expression = modelFactory.castExpression(source,
						this.typeFactory.integerType(), expression);
				break;
			}
			// case INTEGER_POINTER:{
			//
			// }
			case VOID_POINTER:
				// void*->T* or T*->void*
				// ignore, pointer types are all the same
				// all pointer types are using the same symbolic object type
				break;
			case INTEGER_POINTER: {
				expression = modelFactory.castExpression(
						source,
						this.translateABCType(source, scope,
								conversion.getNewType()), expression);
				break;
			}
			default:
				throw new CIVLUnimplementedFeatureException("applying "
						+ conversion + " conversion", source);
			}

			// if (conversion instanceof ArithmeticConversion) {
			// CIVLType oldCIVLType = translateABCType(source, scope, oldType);
			// CIVLType newCIVLType = translateABCType(source, scope, newType);
			//
			// // need equals on Types
			// if (oldCIVLType.isIntegerType() && newCIVLType.isIntegerType()
			// || oldCIVLType.isRealType() && newCIVLType.isRealType()) {
			// // nothing to do
			// } else {
			// // Sometimes the conversion might have been done during
			// // the translating the expression node, for example,
			// // when translating a constant node, so only create a
			// // cast expression if necessary.
			// if (!expression.getExpressionType().equals(newCIVLType))
			// expression = modelFactory.castExpression(source,
			// newCIVLType, expression);
			// }
			// } else if (conversion instanceof CompatiblePointerConversion) {
			// // nothing to do
			// } else if (conversion instanceof ArrayConversion) {
			// if (expressionNode.expressionKind() == ExpressionKind.OPERATOR
			// && ((OperatorNode) expressionNode).getOperator() ==
			// Operator.SUBSCRIPT) {
			// // we will ignore this one here because we want
			// // to keep it as array in subscript expressions
			// } else if (expression.expressionKind() ==
			// Expression.ExpressionKind.ADDRESS_OF
			// || expression.expressionKind() ==
			// Expression.ExpressionKind.ARRAY_LITERAL) {
			// // FIXME: Not sure why this needs to be checked...
			// } else {
			// assert expression instanceof LHSExpression;
			// expression = modelFactory.addressOfExpression(source,
			// modelFactory.subscriptExpression(source,
			// (LHSExpression) expression, modelFactory
			// .integerLiteralExpression(source,
			// BigInteger.ZERO)));
			// }
			//
			// } else if (conversion instanceof
			// CompatibleStructureOrUnionConversion) {
			// // think about this
			// throw new CIVLUnimplementedFeatureException(
			// "compatible structure or union conversion", source);
			// } else if (conversion instanceof FunctionConversion) {
			// } else if (conversion instanceof LvalueConversion) {
			// // nothing to do since ignore qualifiers anyway
			// } else if (conversion instanceof NullPointerConversion) {
			// // result is a null pointer to new type
			// CIVLPointerType newCIVLType = (CIVLPointerType) translateABCType(
			// source, scope, newType);
			//
			// expression = modelFactory.nullPointerExpression(newCIVLType,
			// source);
			// } else if (conversion instanceof PointerBoolConversion) {
			// // pointer type to boolean type: p!=NULL
			// expression = modelFactory.binaryExpression(source,
			// BINARY_OPERATOR.NOT_EQUAL, expression, modelFactory
			// .nullPointerExpression(
			// (CIVLPointerType) expression
			// .getExpressionType(), source));
			// } else if (conversion instanceof VoidPointerConversion) {
			// // void*->T* or T*->void*
			// // ignore, pointer types are all the same
			// // all pointer types are using the same symbolic object type
			// } else if (conversion instanceof RegularRangeToDomainConversion)
			// {
			// expression = modelFactory.recDomainLiteralExpression(
			// source,
			// Arrays.asList(expression),
			// typeFactory.completeDomainType(
			// expression.getExpressionType(), 1));
			// } else
			// throw new CIVLInternalException("Unknown conversion: "
			// + conversion, source);
		}
		return expression;
	}

	private Expression translateRegularRangeNode(RegularRangeNode rangeNode,
			Scope scope) {
		CIVLSource source = modelFactory.sourceOf(rangeNode);
		Expression low = this.translateExpressionNode(rangeNode.getLow(),
				scope, true);
		Expression high = this.translateExpressionNode(rangeNode.getHigh(),
				scope, true);
		Expression step;
		ExpressionNode stepNode = rangeNode.getStep();

		if (stepNode != null)
			step = this.translateExpressionNode(stepNode, scope, true);
		else
			step = modelFactory
					.integerLiteralExpression(source, BigInteger.ONE);
		return modelFactory.regularRangeExpression(source, low, high, step);
	}

	private Expression translateScopeofNode(ScopeOfNode expressionNode,
			Scope scope) {
		ExpressionNode argumentNode = expressionNode.expression();
		Expression argument = translateExpressionNode(argumentNode, scope, true);
		CIVLSource source = modelFactory.sourceOf(expressionNode);

		if (!(argument instanceof LHSExpression))
			throw new CIVLInternalException("expected LHS expression, not "
					+ argument, modelFactory.sourceOf(argumentNode));
		return modelFactory.scopeofExpression(source, (LHSExpression) argument);
	}

	private Expression translateDerivativeExpressionNode(
			DerivativeExpressionNode node, Scope scope) {
		Expression result;
		ExpressionNode functionExpression = node.getFunction();
		Function callee;
		CIVLFunction abstractFunction;
		List<Pair<Variable, IntegerLiteralExpression>> partials = new ArrayList<Pair<Variable, IntegerLiteralExpression>>();
		List<Expression> arguments = new ArrayList<Expression>();

		if (functionExpression instanceof IdentifierExpressionNode) {
			callee = (Function) ((IdentifierExpressionNode) functionExpression)
					.getIdentifier().getEntity();
		} else
			throw new CIVLUnimplementedFeatureException(
					"Function call must use identifier for now: "
							+ functionExpression.getSource());
		abstractFunction = modelBuilder.functionMap.get(callee);
		assert abstractFunction != null;
		assert abstractFunction instanceof AbstractFunction;
		for (int i = 0; i < node.getNumberOfPartials(); i++) {
			PairNode<IdentifierExpressionNode, IntegerConstantNode> partialNode = node
					.getPartial(i);
			Variable partialVariable = null;
			IntegerLiteralExpression partialDegree;

			for (Variable param : abstractFunction.parameters()) {
				if (param.name().name()
						.equals(partialNode.getLeft().getIdentifier().name())) {
					partialVariable = param;
					break;
				}
			}
			assert partialVariable != null;
			partialDegree = modelFactory.integerLiteralExpression(
					modelFactory.sourceOf(partialNode.getRight()), partialNode
							.getRight().getConstantValue().getIntegerValue());
			partials.add(new Pair<Variable, IntegerLiteralExpression>(
					partialVariable, partialDegree));
		}
		for (int i = 0; i < node.getNumberOfArguments(); i++) {
			Expression actual = translateExpressionNode(node.getArgument(i),
					scope, true);

			actual = arrayToPointer(actual);
			arguments.add(actual);
		}
		result = modelFactory.derivativeCallExpression(
				modelFactory.sourceOf(node),
				(AbstractFunction) abstractFunction, partials, arguments);
		return result;
	}

	/**
	 * A function call used as an expression. At present, this should only
	 * happen when the function is an abstract function.
	 * 
	 * @param callNode
	 *            The AST representation of the function call.
	 * @param scope
	 *            The scope containing this expression.
	 * @return The model representation of the function call expression.
	 */
	protected Expression translateFunctionCallExpression(
			FunctionCallNode callNode, Scope scope) {
		Expression result;
		ExpressionNode functionExpression = callNode.getFunction();
		Function callee;
		CIVLFunction civlFunction;
		String functionName;

		if (functionExpression instanceof IdentifierExpressionNode) {
			callee = (Function) ((IdentifierExpressionNode) functionExpression)
					.getIdentifier().getEntity();
		} else
			throw new CIVLUnimplementedFeatureException(
					"Function call must use identifier for now: "
							+ functionExpression.getSource());
		civlFunction = modelBuilder.functionMap.get(callee);
		functionName = civlFunction.name().name();
		assert civlFunction != null;
		if (civlFunction.isAbstractFunction()) {
			List<Expression> arguments = new ArrayList<Expression>();

			for (int i = 0; i < callNode.getNumberOfArguments(); i++) {
				Expression actual = translateExpressionNode(
						callNode.getArgument(i), scope, true);

				actual = arrayToPointer(actual);
				arguments.add(actual);
			}
			result = modelFactory.abstractFunctionCallExpression(
					modelFactory.sourceOf(callNode),
					(AbstractFunction) civlFunction, arguments);
			return result;
		} else
			throw new CIVLUnimplementedFeatureException("Using function call: "
					+ functionName + "as expression.");
	}

	/**
	 * Translate an IdentifierExpressionNode object from the AST into a CIVL
	 * VariableExpression object.
	 * 
	 * @param identifierNode
	 *            The identifier node to be translated.
	 * @param scope
	 *            The scope of the identifier.
	 * @return The CIVL VariableExpression object corresponding to the
	 *         IdentifierExpressionNode
	 */
	private Expression translateIdentifierNode(
			IdentifierExpressionNode identifierNode, Scope scope) {
		CIVLSource source = modelFactory.sourceOf(identifierNode);
		Identifier name = modelFactory.identifier(source, identifierNode
				.getIdentifier().name());
		Expression result;

		if (functionInfo.containsBoundVariable(name)) {
			result = modelFactory.boundVariableExpression(source, name,
					functionInfo.boundVariableType(name));
		} else if (scope.variable(name) != null) {
			VariableExpression varExpression = modelFactory.variableExpression(
					source, scope.variable(name));

			result = varExpression;
		} else if (scope.getFunction(name) != null) {
			result = modelFactory.functionIdentifierExpression(source,
					scope.getFunction(name));
		} else {
			throw new CIVLInternalException("No such variable ", source);
		}
		return result;
	}

	/**
	 * Translate an operator expression from the CIVL AST to the CIVL model.
	 * 
	 * @param operatorNode
	 *            The operator expression.
	 * @param scope
	 *            The (static) scope containing the expression.
	 * @return The model representation of the expression.
	 */
	private Expression translateOperatorNode(OperatorNode operatorNode,
			Scope scope) {
		CIVLSource source = modelFactory.sourceOf(operatorNode);
		Operator operator = operatorNode.getOperator();

		if (operator == Operator.SUBSCRIPT)
			return translateSubscriptNode(operatorNode, scope);

		int numArgs = operatorNode.getNumberOfArguments();
		List<Expression> arguments = new ArrayList<Expression>();
		Expression result = null;
		Expression booleanArg0, booleanArg1;

		for (int i = 0; i < numArgs; i++) {
			arguments.add(translateExpressionNode(operatorNode.getArgument(i),
					scope, true));
		}
		if (numArgs < 1 || numArgs > 3) {
			throw new RuntimeException("Unsupported number of arguments: "
					+ numArgs + " in expression " + operatorNode);
		}
		switch (operatorNode.getOperator()) {
		case ADDRESSOF:
			if (arguments.get(0) instanceof FunctionIdentifierExpression)
				result = arguments.get(0);
			else
				result = modelFactory.addressOfExpression(source,
						(LHSExpression) arguments.get(0));
			break;
		case AT:
			return modelFactory.binaryExpression(source, BINARY_OPERATOR.AT,
					arguments.get(0), arguments.get(1));
		case BIG_O:
			result = modelFactory.unaryExpression(source, UNARY_OPERATOR.BIG_O,
					arguments.get(0));
			break;
		case BITAND:
			result = modelFactory.binaryExpression(source,
					BINARY_OPERATOR.BITAND, arguments.get(0), arguments.get(1));
			break;
		case BITCOMPLEMENT:
			result = modelFactory.binaryExpression(source,
					BINARY_OPERATOR.BITCOMPLEMENT, arguments.get(0),
					arguments.get(1));
			break;
		case BITOR:
			result = modelFactory.binaryExpression(source,
					BINARY_OPERATOR.BITOR, arguments.get(0), arguments.get(1));
			break;
		case BITXOR:
			result = modelFactory.binaryExpression(source,
					BINARY_OPERATOR.BITXOR, arguments.get(0), arguments.get(1));
			break;
		case SHIFTLEFT:
			result = modelFactory.binaryExpression(source,
					BINARY_OPERATOR.SHIFTLEFT, arguments.get(0),
					arguments.get(1));
			break;
		case SHIFTRIGHT:
			result = modelFactory.binaryExpression(source,
					BINARY_OPERATOR.SHIFTRIGHT, arguments.get(0),
					arguments.get(1));
			break;
		case DEREFERENCE:
			Expression pointer = arguments.get(0);

			if (!pointer.getExpressionType().isPointerType()) {
				pointer = this.arrayToPointer(pointer);
			}
			result = modelFactory.dereferenceExpression(source, pointer);
			break;
		case CONDITIONAL:
			try {
				booleanArg0 = modelFactory.booleanExpression(arguments.get(0));
			} catch (ModelFactoryException err) {
				throw new CIVLSyntaxException(
						"The first argument of the conditional expression "
								+ arguments.get(0) + " is of "
								+ arguments.get(0).getExpressionType()
								+ "type which cannot be converted to "
								+ "boolean type.", arguments.get(0).getSource());
			}
			result = modelFactory.conditionalExpression(source, booleanArg0,
					arguments.get(1), arguments.get(2));
			modelFactory
					.addConditionalExpression((ConditionalExpression) result);
			break;
		case DIV:
			result = modelFactory.binaryExpression(source,
					BINARY_OPERATOR.DIVIDE,
					modelFactory.numericExpression(arguments.get(0)),
					modelFactory.numericExpression(arguments.get(1)));
			break;
		case GT:
			result = modelFactory.binaryExpression(source,
					BINARY_OPERATOR.LESS_THAN,
					modelFactory.numericExpression(arguments.get(1)),
					modelFactory.numericExpression(arguments.get(0)));
			break;
		case GTE:
			result = modelFactory.binaryExpression(source,
					BINARY_OPERATOR.LESS_THAN_EQUAL,
					modelFactory.numericExpression(arguments.get(1)),
					modelFactory.numericExpression(arguments.get(0)));
			break;
		case IMPLIES:
			try {
				booleanArg0 = modelFactory.booleanExpression(arguments.get(0));
			} catch (ModelFactoryException err) {
				throw new CIVLSyntaxException(
						"The first argument of the implies expression "
								+ arguments.get(0) + " is of "
								+ arguments.get(0).getExpressionType()
								+ "type which cannot be converted to "
								+ "boolean type.", arguments.get(0).getSource());
			}
			try {
				booleanArg1 = modelFactory.booleanExpression(arguments.get(1));
			} catch (ModelFactoryException err) {
				throw new CIVLSyntaxException(
						"The second argument of the implies expression "
								+ arguments.get(1) + " is of "
								+ arguments.get(1).getExpressionType()
								+ "type which cannot be converted to "
								+ "boolean type.", arguments.get(1).getSource());
			}
			result = modelFactory.binaryExpression(source,
					BINARY_OPERATOR.IMPLIES, booleanArg0, booleanArg1);
			break;
		case LAND:
			try {
				booleanArg0 = modelFactory.booleanExpression(arguments.get(0));
			} catch (ModelFactoryException err) {
				throw new CIVLSyntaxException(
						"The first argument of the logical and expression "
								+ arguments.get(0) + " is of "
								+ arguments.get(0).getExpressionType()
								+ "type which cannot be converted to "
								+ "boolean type.", arguments.get(0).getSource());
			}
			try {
				booleanArg1 = modelFactory.booleanExpression(arguments.get(1));
			} catch (ModelFactoryException err) {
				throw new CIVLSyntaxException(
						"The first argument of the logical and expression "
								+ arguments.get(1) + " is of "
								+ arguments.get(1).getExpressionType()
								+ "type which cannot be converted to "
								+ "boolean type.", arguments.get(1).getSource());
			}
			result = modelFactory.binaryExpression(source, BINARY_OPERATOR.AND,
					booleanArg0, booleanArg1);
			break;
		case LOR:
			try {
				booleanArg0 = modelFactory.booleanExpression(arguments.get(0));
			} catch (ModelFactoryException err) {
				throw new CIVLSyntaxException(
						"The first argument of the logical or expression "
								+ arguments.get(0) + " is of "
								+ arguments.get(0).getExpressionType()
								+ "type which cannot be converted to "
								+ "boolean type.", arguments.get(0).getSource());
			}
			try {
				booleanArg1 = modelFactory.booleanExpression(arguments.get(1));
			} catch (ModelFactoryException err) {
				throw new CIVLSyntaxException(
						"The first argument of the conditional expression "
								+ arguments.get(1) + " is of "
								+ arguments.get(1).getExpressionType()
								+ "type which cannot be converted to "
								+ "boolean type.", arguments.get(1).getSource());
			}
			result = modelFactory.binaryExpression(source, BINARY_OPERATOR.OR,
					booleanArg0, booleanArg1);
			break;
		case LT:
			result = modelFactory.binaryExpression(source,
					BINARY_OPERATOR.LESS_THAN,
					modelFactory.numericExpression(arguments.get(0)),
					modelFactory.numericExpression(arguments.get(1)));
			break;
		case LTE:
			result = modelFactory.binaryExpression(source,
					BINARY_OPERATOR.LESS_THAN_EQUAL,
					modelFactory.numericExpression(arguments.get(0)),
					modelFactory.numericExpression(arguments.get(1)));
			break;
		case MINUS:
			result = translateMinusOperation(source,
					modelFactory.numericExpression(arguments.get(0)),
					modelFactory.numericExpression(arguments.get(1)));
			break;
		case MOD:
			result = modelFactory.binaryExpression(source,
					BINARY_OPERATOR.MODULO,
					modelFactory.numericExpression(arguments.get(0)),
					modelFactory.numericExpression(arguments.get(1)));
			break;
		case EQUALS:
		case NEQ: {
			Expression arg0 = arguments.get(0), arg1 = arguments.get(1);
			CIVLType arg0Type = arg0.getExpressionType(), arg1Type = arg1
					.getExpressionType();

			if (arg0Type.isNumericType() && arg1Type.isBoolType())
				arg1 = modelFactory.numericExpression(arg1);
			else if (arg0Type.isBoolType() && arg1Type.isNumericType())
				arg0 = modelFactory.numericExpression(arg0);
			result = modelFactory.binaryExpression(source, operatorNode
					.getOperator() == Operator.EQUALS ? BINARY_OPERATOR.EQUAL
					: BINARY_OPERATOR.NOT_EQUAL, arg0, arg1);
			break;
		}
		case NOT: {
			// CIVLType argType = arguments.get(0).getExpressionType();
			try {
				booleanArg0 = modelFactory.booleanExpression(arguments.get(0));
			} catch (ModelFactoryException err) {
				throw new CIVLSyntaxException(
						"The argument of the logical not expression "
								+ arguments.get(0) + " is of "
								+ arguments.get(0).getExpressionType()
								+ "type which cannot be converted to "
								+ "boolean type.", arguments.get(0).getSource());
			}
			result = modelFactory.unaryExpression(source, UNARY_OPERATOR.NOT,
					booleanArg0);
			// if (argType.isIntegerType()) {
			// result = modelFactory.castExpression(source, argType, result);
			// }
		}
			break;
		case PLUS:
			result = translatePlusOperation(source,
					modelFactory.numericExpression(arguments.get(0)),
					modelFactory.numericExpression(arguments.get(1)));
			break;
		case SUBSCRIPT:
			throw new CIVLInternalException("unreachable", source);
		case TIMES:
			result = modelFactory.binaryExpression(source,
					BINARY_OPERATOR.TIMES,
					modelFactory.numericExpression(arguments.get(0)),
					modelFactory.numericExpression(arguments.get(1)));
			break;
		case UNARYMINUS:
			result = modelFactory.unaryExpression(source,
					UNARY_OPERATOR.NEGATIVE,
					modelFactory.numericExpression(arguments.get(0)));
			break;
		case UNARYPLUS:
			result = modelFactory.numericExpression(arguments.get(0));
			break;
		default:
			throw new CIVLUnimplementedFeatureException(
					"Unsupported operator: " + operatorNode.getOperator()
							+ " in expression " + operatorNode);
		}
		return result;
	}

	/**
	 * Translate plus operation into an expression, as a helper method for
	 * {@link #translateOperatorNode(OperatorNode, Scope)}.
	 * 
	 * @param source
	 *            The CIVL source of the plus operator.
	 * @param arg0
	 *            The first argument of the plus operation.
	 * @param arg1
	 *            The second argument of the plus operation.
	 * @return The CIVL expression of the plus operation.
	 */
	private Expression translatePlusOperation(CIVLSource source,
			Expression arg0, Expression arg1) {
		CIVLType type0 = arg0.getExpressionType();
		CIVLType type1 = arg1.getExpressionType();
		boolean isNumeric0 = type0.isNumericType() || type0.isScopeType();
		boolean isNumeric1 = type1.isNumericType() || type1.isScopeType();

		if (isNumeric0 && isNumeric1) {
			return modelFactory.binaryExpression(source, BINARY_OPERATOR.PLUS,
					arg0, arg1);
		} else {
			Expression pointer, offset;

			if (isNumeric1) {
				pointer = arrayToPointer(arg0);
				offset = arg1;
			} else if (isNumeric0) {
				pointer = arrayToPointer(arg1);
				offset = arg0;
			} else
				throw new CIVLInternalException(
						"Expected at least one numeric argument", source);
			if (!pointer.getExpressionType().isPointerType())
				throw new CIVLInternalException(
						"Expected expression of pointer type",
						pointer.getSource());
			if (!offset.getExpressionType().isIntegerType())
				throw new CIVLInternalException(
						"Expected expression of integer type",
						offset.getSource());
			return modelFactory.binaryExpression(source,
					BINARY_OPERATOR.POINTER_ADD, pointer, offset);
		}
	}

	/**
	 * Translate plus operation into an expression, as a helper method for
	 * {@link #translateOperatorNode(OperatorNode, Scope)}.
	 * 
	 * @param source
	 *            The CIVL source of the minus operator.
	 * @param arg0
	 *            The first argument of the minus operation.
	 * @param arg1
	 *            The second argument of the minus operation.
	 * @return The CIVL expression of the minus operation.
	 */
	private Expression translateMinusOperation(CIVLSource source,
			Expression arg0, Expression arg1) {
		CIVLType type0 = arg0.getExpressionType();
		CIVLType type1 = arg1.getExpressionType();
		boolean isNumeric0 = type0.isNumericType() || type0.isScopeType();
		boolean isNumeric1 = type1.isNumericType() || type1.isScopeType();

		if (isNumeric0 && isNumeric1) {
			return modelFactory.binaryExpression(source, BINARY_OPERATOR.MINUS,
					arg0, arg1);
		} else {
			Expression pointer, rightOperand;// , offset;
			// boolean isSub = false;

			rightOperand = null;
			// // offset = null;
			// if (isNumeric1) {
			// pointer = arrayToPointer(arg0);
			// // offset = arg1;
			// } else if (isNumeric0) {
			// pointer = arrayToPointer(arg1);
			// // offset = arg0;
			// } else {
			pointer = arrayToPointer(arg0);
			rightOperand = arrayToPointer(arg1);
			// isSub = true;
			// }
			if (!pointer.getExpressionType().isPointerType())
				throw new CIVLInternalException(
						"Expected expression of pointer type",
						pointer.getSource());
			// if (isSub) {
			// if (!rightOperand.getExpressionType().isPointerType())
			// throw new CIVLInternalException(
			// "Expected expression of pointer type",
			// rightOperand.getSource());
			return modelFactory.binaryExpression(source,
					BINARY_OPERATOR.POINTER_SUBTRACT, pointer, rightOperand);
			// } else {
			// if (!offset.getExpressionType().isIntegerType())
			// throw new CIVLInternalException(
			// "Expected expression of integer type",
			// offset.getSource());
			// return modelFactory.binaryExpression(source,
			// BINARY_OPERATOR.POINTER_ADD, pointer, modelFactory
			// .unaryExpression(offset.getSource(),
			// UNARY_OPERATOR.NEGATIVE, offset));
			// }

		}
	}

	/**
	 * Translate a QuantifiedExpressionNode from AST into a CIVL Quantified
	 * expression
	 * 
	 * @param expressionNode
	 *            The quantified expression node
	 * @param scope
	 *            The scope
	 * @return the CIVL QuantifiedExpression
	 */
	private Expression translateQuantifiedExpressionNode(
			QuantifiedExpressionNode expressionNode, Scope scope) {
		QuantifiedExpression result;
		Quantifier quantifier;
		Identifier variableName;
		TypeNode variableTypeNode;
		CIVLType variableType;
		Expression quantifiedExpression;
		CIVLSource source = modelFactory.sourceOf(expressionNode.getSource());

		variableName = modelFactory.identifier(
				modelFactory.sourceOf(expressionNode.variable().getSource()),
				expressionNode.variable().getName());
		variableTypeNode = expressionNode.variable().getTypeNode();
		variableType = translateABCType(
				modelFactory.sourceOf(variableTypeNode.getSource()), scope,
				variableTypeNode.getType());
		functionInfo.addBoundVariable(variableName, variableType);
		switch (expressionNode.quantifier()) {
		case EXISTS:
			quantifier = Quantifier.EXISTS;
			break;
		case FORALL:
			quantifier = Quantifier.FORALL;
			break;
		case UNIFORM:
			quantifier = Quantifier.UNIFORM;
			break;
		default:
			throw new CIVLUnimplementedFeatureException("quantifier "
					+ expressionNode.quantifier(), source);
		}
		if (expressionNode.isRange()) {
			Expression lower = translateExpressionNode(expressionNode.lower(),
					scope, true);
			Expression upper = translateExpressionNode(expressionNode.upper(),
					scope, true);

			quantifiedExpression = translateExpressionNode(
					expressionNode.expression(), scope, true);
			result = modelFactory.quantifiedExpression(source, quantifier,
					variableName, variableType, lower, upper,
					quantifiedExpression);
		} else {
			Expression restriction = translateExpressionNode(
					expressionNode.restriction(), scope, true);

			quantifiedExpression = translateExpressionNode(
					expressionNode.expression(), scope, true);
			result = modelFactory.quantifiedExpression(source, quantifier,
					variableName, variableType, restriction,
					quantifiedExpression);
		}
		functionInfo.popBoundVariableStack();
		return result;
	}

	/**
	 * Translate a SizeofNode object from AST into a CIVL expression object
	 * 
	 * @param sizeofNode
	 *            The size of node
	 * @param scope
	 *            The scope
	 * @return the CIVL Sizeof expression
	 */
	private Expression translateSizeofNode(SizeofNode sizeofNode, Scope scope) {
		SizeableNode argNode = sizeofNode.getArgument();
		CIVLSource source = modelFactory.sourceOf(sizeofNode);
		Expression result;

		switch (argNode.nodeKind()) {
		case TYPE:
			TypeNode typeNode = (TypeNode) argNode;
			CIVLType type = translateABCType(modelFactory.sourceOf(typeNode),
					scope, typeNode.getType());

			result = modelFactory.sizeofTypeExpression(source, type);
			break;
		case EXPRESSION:
			Expression argument = translateExpressionNode(
					(ExpressionNode) argNode, scope, true);

			result = modelFactory.sizeofExpressionExpression(source, argument);
			break;
		default:
			throw new CIVLInternalException("Unknown kind of SizeofNode: "
					+ sizeofNode, source);
		}
		return result;
	}

	private Expression translateRemoteReferenceNode(
			RemoteExpressionNode expressionNode, Scope scope) {
		ExpressionNode processNode = expressionNode.getProcessExpression();
		IdentifierExpressionNode identifierNode = expressionNode
				.getIdentifierNode();
		VariableExpression variable;
		Expression process;

		variable = (VariableExpression) this.translateIdentifierNode(
				identifierNode, scope);
		process = this.translateExpressionNode(processNode, scope, false);
		return modelFactory
				.remoteExpression(modelFactory.sourceOf(expressionNode),
						process, variable, scope);
	}

	/**
	 * Translates an AST subscript node e1[e2] to a CIVL expression. The result
	 * will either be a CIVL subscript expression (if e1 has array type) or a
	 * CIVL expression of the form *(e1+e2) or *(e2+e1).
	 * 
	 * @param subscriptNode
	 *            an AST node with operator SUBSCRIPT
	 * @param scope
	 *            scope in which this expression occurs
	 * @return the equivalent CIVL expression
	 */
	private Expression translateSubscriptNode(OperatorNode subscriptNode,
			Scope scope) {
		CIVLSource source = modelFactory.sourceOf(subscriptNode);
		ExpressionNode leftNode = subscriptNode.getArgument(0);
		ExpressionNode rightNode = subscriptNode.getArgument(1);
		Expression lhs = translateExpressionNode(leftNode, scope, false);
		Expression rhs = translateExpressionNode(rightNode, scope, true);
		CIVLType lhsType = lhs.getExpressionType();
		Expression result;

		if (lhsType.isArrayType()) {
			if (!(lhs instanceof LHSExpression))
				throw new CIVLInternalException(
						"Expected expression with array type to be LHS",
						lhs.getSource());
			result = modelFactory.subscriptExpression(source,
					(LHSExpression) lhs, rhs);
		} else {
			CIVLType rhsType = rhs.getExpressionType();
			Expression pointerExpr, indexExpr;

			if (lhsType.isPointerType()) {
				if (!rhsType.isIntegerType())
					throw new CIVLInternalException(
							"Expected expression of integer type",
							rhs.getSource());
				pointerExpr = lhs;
				indexExpr = rhs;
			} else if (lhsType.isIntegerType()) {
				if (!rhsType.isPointerType())
					throw new CIVLInternalException(
							"Expected expression of pointer type",
							rhs.getSource());
				pointerExpr = rhs;
				indexExpr = lhs;
			} else
				throw new CIVLInternalException(
						"Expected one argument of integer type and one of pointer type",
						source);
			result = modelFactory.dereferenceExpression(source, modelFactory
					.binaryExpression(source, BINARY_OPERATOR.POINTER_ADD,
							pointerExpr, indexExpr));
		}
		return result;
	}

	/* *********************************************************************
	 * Translating ABC Type into CIVL Type
	 * *********************************************************************
	 */

	/**
	 * Translate the extent of an array type to an expression
	 * 
	 * @param source
	 *            The CIVL source
	 * @param arrayType
	 *            The array type
	 * @param scope
	 *            The scope
	 * @return the expression representing the extent
	 * */
	private Expression arrayExtent(CIVLSource source, ArrayType arrayType,
			Scope scope) {
		Expression result;

		if (arrayType.isComplete()) {
			ExpressionNode variableSize = arrayType.getVariableSize();

			if (variableSize != null) {
				result = translateExpressionNode(variableSize, scope, true);
			} else {
				IntegerValue constantSize = arrayType.getConstantSize();

				if (constantSize != null)
					result = modelFactory.integerLiteralExpression(source,
							constantSize.getIntegerValue());
				else
					throw new CIVLInternalException(
							"Complete array type has neither constant size nor variable size: "
									+ arrayType, source);
			}
		} else
			result = null;
		return result;
	}

	/**
	 * Calculate the index of a field in a struct type
	 * 
	 * @param fieldIdentifier
	 *            The identifier of the field
	 * @return The index of the field
	 */
	private int getFieldIndex(IdentifierNode fieldIdentifier) {
		Entity entity = fieldIdentifier.getEntity();
		EntityKind kind = entity.getEntityKind();

		if (kind == EntityKind.FIELD) {
			Field field = (Field) entity;

			return field.getMemberIndex();
		} else {
			throw new CIVLInternalException(
					"getFieldIndex given identifier that does not correspond to field: ",
					modelFactory.sourceOf(fieldIdentifier));
		}
	}

	/**
	 * Translate ABC basic types into CIVL types
	 * 
	 * @param source
	 *            The CIVL source
	 * @param basicType
	 *            The basic ABC type
	 * @return CIVL type
	 */
	private CIVLType translateABCBasicType(CIVLSource source,
			StandardBasicType basicType) {
		switch (basicType.getBasicTypeKind()) {
		case SHORT:
		case UNSIGNED_SHORT:
		case INT:
		case UNSIGNED:
		case LONG:
		case UNSIGNED_LONG:
		case LONG_LONG:
		case UNSIGNED_LONG_LONG:
			return typeFactory.integerType();
		case FLOAT:
		case DOUBLE:
		case LONG_DOUBLE:
		case REAL:
			return typeFactory.realType();
		case BOOL:
			return typeFactory.booleanType();
		case CHAR:
		case UNSIGNED_CHAR:
			return typeFactory.charType();
		case DOUBLE_COMPLEX:
		case FLOAT_COMPLEX:
		case LONG_DOUBLE_COMPLEX:
		case SIGNED_CHAR:
		default:
			throw new CIVLUnimplementedFeatureException("types of kind "
					+ basicType.kind(), source);
		}
	}

	/**
	 * Translate ABC struct or union type into CIVL type
	 * 
	 * @param source
	 *            The CIVL source
	 * @param scope
	 *            The scope
	 * @param type
	 *            The ABC struct or union type
	 * @return CIVL type of struct or union
	 */
	private CIVLType translateABCStructureOrUnionType(CIVLSource source,
			Scope scope, StructureOrUnionType type) {
		String tag = type.getTag();
		CIVLStructOrUnionType result;
		int numFields;
		StructOrUnionField[] civlFields;

		if (tag == null) {
			if (type.isStruct())
				tag = "__struct_" + modelBuilder.anonymousStructCounter + "__";
			else
				tag = "__union_" + modelBuilder.anonymousStructCounter + "__";
			modelBuilder.anonymousStructCounter++;
		}
		// civlc.h defines $proc as struct __proc__, etc.
		switch (tag) {
		case ModelConfiguration.PROC_TYPE:
			return typeFactory.processType();
		case ModelConfiguration.HEAP_TYPE:
			return modelBuilder.heapType;
		case ModelConfiguration.DYNAMIC_TYPE:
			return typeFactory.dynamicType();
		case ModelConfiguration.BUNDLE_TYPE:
			return modelBuilder.bundleType;
		default:
		}
		result = typeFactory.structOrUnionType(
				modelFactory.identifier(source, tag), type.isStruct());
		numFields = type.getNumFields();
		civlFields = new StructOrUnionField[numFields];
		modelBuilder.typeMap.put(type, result);
		for (int i = 0; i < numFields; i++) {
			Field field = type.getField(i);
			String name = field.getName();
			Type fieldType = field.getType();
			CIVLType civlFieldType = translateABCType(source, scope, fieldType);
			Identifier identifier = modelFactory.identifier(modelFactory
					.sourceOf(field.getDefinition().getIdentifier()), name);
			StructOrUnionField civlField = typeFactory.structField(identifier,
					civlFieldType);

			civlFields[i] = civlField;
		}
		result.complete(civlFields);
		switch (tag) {
		case ModelConfiguration.MESSAGE_TYPE:
			modelBuilder.messageType = result;
			break;
		case ModelConfiguration.QUEUE_TYPE:
			modelBuilder.queueType = result;
			break;
		case ModelConfiguration.PTHREAD_POOL:
		case ModelConfiguration.PTHREAD_GPOOL:
			result.setHandleObjectType(true);
			typeFactory.addSystemType(tag, result);
			modelBuilder.handledObjectTypes.add(result);
			break;
		case ModelConfiguration.BARRIER_TYPE:
			result.setHandleObjectType(true);
			typeFactory.addSystemType(tag, result);
			modelBuilder.barrierType = result;
			modelBuilder.handledObjectTypes.add(result);
			break;
		case ModelConfiguration.GBARRIER_TYPE:
			result.setHandleObjectType(true);
			typeFactory.addSystemType(tag, result);
			modelBuilder.gbarrierType = result;
			modelBuilder.handledObjectTypes.add(result);
			break;
		case ModelConfiguration.INT_ITER_TYPE:
			typeFactory.addSystemType(tag, result);
			// result.setHandleObjectType(true);
			modelBuilder.intIterType = result;
			modelBuilder.handledObjectTypes.add(result);
			break;
		case ModelConfiguration.COMM_TYPE:
			typeFactory.addSystemType(tag, result);
			result.setHandleObjectType(true);
			modelBuilder.commType = result;
			modelBuilder.handledObjectTypes.add(result);
			break;
		case ModelConfiguration.GCOMM_TYPE:
			typeFactory.addSystemType(tag, result);
			result.setHandleObjectType(true);
			modelBuilder.gcommType = result;
			modelBuilder.handledObjectTypes.add(result);
			break;
		case ModelConfiguration.FILE_SYSTEM_TYPE:
			// result.setHandleObjectType(true);
			modelBuilder.basedFilesystemType = result;
			typeFactory.addSystemType(tag, result);
			modelBuilder.handledObjectTypes.add(result);
			break;
		case ModelConfiguration.REAL_FILE_TYPE:
			modelBuilder.fileType = result;
			typeFactory.addSystemType(tag, result);
			break;
		case ModelConfiguration.FILE_STREAM_TYPE:
			typeFactory.addSystemType(tag, result);
			modelBuilder.FILEtype = result;
			modelBuilder.handledObjectTypes.add(result);
			break;
		case ModelConfiguration.TM_TYPE:
			// modelBuilder.handledObjectTypes.add(result);
			typeFactory.addSystemType(tag, result);
			break;
		case ModelConfiguration.COLLECT_RECORD_TYPE:
			typeFactory.addSystemType(tag, result);
			result.setHandleObjectType(false);
			modelBuilder.collectRecordType = result;
			// modelBuilder.handledObjectTypes.add(result);
			break;
		case ModelConfiguration.GCOLLECT_CHECKER_TYPE:
			typeFactory.addSystemType(tag, result);
			result.setHandleObjectType(true);
			modelBuilder.gcollectCheckerType = result;
			modelBuilder.handledObjectTypes.add(result);
			break;
		case ModelConfiguration.COLLECT_CHECKER_TYPE:
			typeFactory.addSystemType(tag, result);
			result.setHandleObjectType(true);
			modelBuilder.collectCheckerType = result;
			modelBuilder.handledObjectTypes.add(result);
			break;
		default:
			// TODO: set default case
		}
		return result;
	}

	/**
	 * Working on replacing process type with this.
	 * 
	 * @param source
	 *            The CIVL source
	 * @param scope
	 *            The scope
	 * @param abcType
	 *            The ABC type
	 * @return The CIVL type
	 */
	protected CIVLType translateABCType(CIVLSource source, Scope scope,
			Type abcType) {
		CIVLType result = modelBuilder.typeMap.get(abcType);

		if (result == null) {
			TypeKind kind = abcType.kind();

			switch (kind) {
			case ARRAY: {
				ArrayType arrayType = (ArrayType) abcType;
				CIVLType elementType = translateABCType(source, scope,
						arrayType.getElementType());
				Expression extent = arrayExtent(source, arrayType, scope);

				if (extent != null)
					result = typeFactory.completeArrayType(elementType, extent);
				else
					result = typeFactory.incompleteArrayType(elementType);
				break;
			}
			case BASIC:
				result = translateABCBasicType(source,
						(StandardBasicType) abcType);
				break;
			case HEAP:
				result = typeFactory.pointerType(modelBuilder.heapType);
				break;
			case OTHER_INTEGER:
				result = typeFactory.integerType();
				break;
			case POINTER: {
				PointerType pointerType = (PointerType) abcType;
				Type referencedType = pointerType.referencedType();
				CIVLType baseType = translateABCType(source, scope,
						referencedType);

				// if (baseType.isFunction())
				// result = baseType;
				// else
				result = typeFactory.pointerType(baseType);
				break;
			}
			case PROCESS:
				result = typeFactory.processType();
				break;
			case SCOPE:
				result = typeFactory.scopeType();
				break;
			case QUALIFIED:
				result = translateABCType(source, scope,
						((QualifiedObjectType) abcType).getBaseType());
				break;
			case STRUCTURE_OR_UNION:
				result = translateABCStructureOrUnionType(source, scope,
						(StructureOrUnionType) abcType);
				// type already entered into map, so just return:
				return result;
			case VOID:
				result = typeFactory.voidType();
				break;
			case ENUMERATION:
				return translateABCEnumerationType(source, scope,
						(EnumerationType) abcType);
			case FUNCTION:
				return translateABCFunctionType(source, scope,
						(FunctionType) abcType);
			case RANGE:
				return typeFactory.rangeType();
			case DOMAIN:
				return translateABCDomainType(source, scope,
						(DomainType) abcType);
			case ATOMIC:
				throw new CIVLUnimplementedFeatureException("Type " + abcType,
						source);
			default:
				throw new CIVLInternalException("Unknown type: " + abcType,
						source);
			}
			modelBuilder.typeMap.put(abcType, result);
		}
		return result;
	}

	private CIVLType translateABCDomainType(CIVLSource source, Scope scope,
			DomainType domainType) {
		if (domainType.hasDimension())
			return typeFactory.completeDomainType(typeFactory.rangeType(),
					domainType.getDimension());
		else
			return typeFactory.domainType(typeFactory.rangeType());
	}

	/**
	 * Translates ABC function type.
	 * 
	 * @param source
	 *            The source code element to be used for error report.
	 * @param scope
	 *            The scope of the function type.
	 * @param abcType
	 *            The ABC representation of the function type.
	 * @return The CIVL function type translated from the ABC function type.
	 */
	private CIVLType translateABCFunctionType(CIVLSource source, Scope scope,
			FunctionType abcType) {
		CIVLType returnType = translateABCType(source, scope,
				abcType.getReturnType());
		int numberOfParameters = abcType.getNumParameters();
		CIVLType[] paraTypes = new CIVLType[numberOfParameters];

		for (int i = 0; i < numberOfParameters; i++) {
			paraTypes[i] = translateABCType(source, scope,
					abcType.getParameterType(i));
		}
		return typeFactory.functionType(returnType, paraTypes);
	}

	/**
	 * Translate type node that is typedef, struct or union.
	 * <p>
	 * The method {@link CIVLType#hasState} in {@link CIVLType} will return
	 * <code>true</code> for any type which contains an array with extent which
	 * is not constant. We associate to these types a state variable that can be
	 * set and get.
	 * <p>
	 * When you come across a typedef, or complete struct or union def,
	 * construct the CIVL type <code>t</code> as usual. If
	 * <code>t.hasState()</code>, insert into the model at the current scope a
	 * variable <code>__struct_foo__</code>, <code>__union_foo__</code>, or
	 * <code>__typedef_foo__</code> of type "CIVL dynamic type". Set the state
	 * variable in <code>t</code> to this variable. At the point of definition,
	 * insert a model assignment statement,
	 * <code>__struct_foo__ = DynamicTypeOf(t)</code> (for example).
	 * 
	 * @param sourceLocation
	 *            The location
	 * @param scope
	 *            The scope
	 * @param typeNode
	 *            The type node
	 * @return the fragment
	 */
	private Fragment translateCompoundTypeNode(Location sourceLocation,
			Scope scope, TypeNode typeNode) {
		Fragment result = null;
		String prefix;
		String tag;
		CIVLType type = translateABCType(modelFactory.sourceOf(typeNode),
				scope, typeNode.getType());
		CIVLSource civlSource = modelFactory.sourceOf(typeNode);

		if (typeNode instanceof StructureOrUnionTypeNode) {
			StructureOrUnionTypeNode structOrUnionTypeNode = (StructureOrUnionTypeNode) typeNode;

			if (structOrUnionTypeNode.isStruct())
				prefix = "__struct_";
			else
				prefix = "__union_";
			// This is null if this is a "declaration" but not the
			// "definition".
			if (((StructureOrUnionTypeNode) typeNode).getStructDeclList() == null)
				return result;
			if (!(type instanceof CIVLStructOrUnionType))
				throw new CIVLInternalException("unexpected type: " + type,
						civlSource);
			else {
				tag = ((CIVLStructOrUnionType) type).name().name();
			}
		} else {
			prefix = "__typedef_";
			if (!(typeNode instanceof EnumerationTypeNode))
				tag = ((TypedefDeclarationNode) typeNode.parent()).getName();
			else
				tag = "";
		}
		if (type.hasState()) {
			Variable variable;
			String name = prefix + tag + "__";
			Identifier identifier = modelFactory.identifier(civlSource, name);
			int vid = scope.numVariables();
			LHSExpression lhs;
			Expression rhs = modelFactory.dynamicTypeOfExpression(civlSource,
					type);

			variable = modelFactory.variable(civlSource,
					typeFactory.dynamicType(), identifier, vid);
			lhs = modelFactory.variableExpression(civlSource, variable);
			scope.addVariable(variable);
			type.setStateVariable(variable);
			if (sourceLocation == null)
				sourceLocation = modelFactory.location(
						modelFactory.sourceOfBeginning(typeNode), scope);
			result = new CommonFragment(modelFactory.assignStatement(
					civlSource, sourceLocation, lhs, rhs, true));
		}
		return result;
	}

	private void setFunction(CIVLFunction function) {
		this.function = function;
	}
}
