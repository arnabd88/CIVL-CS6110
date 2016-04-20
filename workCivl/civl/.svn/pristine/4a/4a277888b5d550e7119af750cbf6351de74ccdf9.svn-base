package edu.udel.cis.vsl.civl.model.common;

import java.io.File;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.udel.cis.vsl.abc.ast.conversion.IF.ArithmeticConversion;
import edu.udel.cis.vsl.abc.ast.conversion.IF.ArrayConversion;
import edu.udel.cis.vsl.abc.ast.conversion.IF.CompatiblePointerConversion;
import edu.udel.cis.vsl.abc.ast.conversion.IF.CompatibleStructureOrUnionConversion;
import edu.udel.cis.vsl.abc.ast.conversion.IF.Conversion;
import edu.udel.cis.vsl.abc.ast.conversion.IF.FunctionConversion;
import edu.udel.cis.vsl.abc.ast.conversion.IF.LvalueConversion;
import edu.udel.cis.vsl.abc.ast.conversion.IF.NullPointerConversion;
import edu.udel.cis.vsl.abc.ast.conversion.IF.PointerBoolConversion;
import edu.udel.cis.vsl.abc.ast.conversion.IF.VoidPointerConversion;
import edu.udel.cis.vsl.abc.ast.entity.IF.Entity;
import edu.udel.cis.vsl.abc.ast.entity.IF.Entity.EntityKind;
import edu.udel.cis.vsl.abc.ast.entity.IF.Enumerator;
import edu.udel.cis.vsl.abc.ast.entity.IF.Field;
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
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.DeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.EnsuresNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.InitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.RequiresNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.ScopeParameterizedDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.TypedefDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ArrowNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.CastNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.CompoundLiteralNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.DerivativeExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.DotNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.EnumerationConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.HereOrRootNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IntegerConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.QuantifiedExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ScopeOfNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.SizeableNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.SizeofNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.SpawnNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.StringLiteralNode;
import edu.udel.cis.vsl.abc.ast.node.IF.label.LabelNode;
import edu.udel.cis.vsl.abc.ast.node.IF.label.OrdinaryLabelNode;
import edu.udel.cis.vsl.abc.ast.node.IF.label.SwitchLabelNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.AssumeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.AtomicNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ChooseStatementNode;
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
import edu.udel.cis.vsl.abc.ast.node.IF.statement.SwitchNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.WaitNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.WhenNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.EnumerationTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.FunctionTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.StructureOrUnionTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode.TypeNodeKind;
import edu.udel.cis.vsl.abc.ast.node.common.declaration.CommonFunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.type.IF.ArrayType;
import edu.udel.cis.vsl.abc.ast.type.IF.EnumerationType;
import edu.udel.cis.vsl.abc.ast.type.IF.FunctionType;
import edu.udel.cis.vsl.abc.ast.type.IF.PointerType;
import edu.udel.cis.vsl.abc.ast.type.IF.QualifiedObjectType;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.StructureOrUnionType;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.ast.type.IF.Type.TypeKind;
import edu.udel.cis.vsl.abc.ast.type.common.CommonCharType;
import edu.udel.cis.vsl.abc.ast.value.IF.CharacterValue;
import edu.udel.cis.vsl.abc.ast.value.IF.IntegerValue;
import edu.udel.cis.vsl.abc.ast.value.IF.Value;
import edu.udel.cis.vsl.abc.token.IF.CToken;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.StringLiteral;
import edu.udel.cis.vsl.civl.err.CIVLException;
import edu.udel.cis.vsl.civl.err.CIVLInternalException;
import edu.udel.cis.vsl.civl.err.CIVLSyntaxException;
import edu.udel.cis.vsl.civl.err.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.AbstractFunction;
import edu.udel.cis.vsl.civl.model.IF.AccuracyAssumptionBuilder;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Fragment;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ArrayLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression.BINARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.IntegerLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.LiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.QuantifiedExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.QuantifiedExpression.Quantifier;
import edu.udel.cis.vsl.civl.model.IF.expression.SystemFunctionCallExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression.UNARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.MallocStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ReturnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPointerType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPrimitiveType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPrimitiveType.PrimitiveTypeKind;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLStructOrUnionType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.type.StructOrUnionField;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.model.common.expression.CommonExpression;
import edu.udel.cis.vsl.civl.model.common.location.CommonLocation.AtomicKind;
import edu.udel.cis.vsl.civl.model.common.statement.StatementSet;
import edu.udel.cis.vsl.civl.util.Pair;
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

	private static final String BUNDLE_TYPE = "__bundle__";

	private static final String COMM_TYPE = "__comm__";

	private static final String DYNAMIC_TYPE = "__dynamic__";

	private static final String GCOMM_TYPE = "__gcomm__";

	private static final String HEAP_TYPE = "__heap__";

	private static final String MESSAGE_TYPE = "__message__";

	private static final String PROC_TYPE = "__proc__";

	private static final String QUEUE_TYPE = "__queue__";

	/* ************************** Instance Fields ************************** */

	/**
	 * Store temporary information of the function being processed
	 */
	protected FunctionInfo functionInfo;

	/**
	 * The unique model factory to be used in the system.
	 */
	private ModelFactory modelFactory;

	/**
	 * Keep track of the number of incomplete $atom block during translation.
	 */
	private int atomCount = 0;

	/**
	 * The unique model builder of the system.
	 */
	private ModelBuilderWorker modelBuilder;

	/**
	 * The AST node of the function body, which is to be used for translation.
	 */
	protected StatementNode functionBodyNode;

	/**
	 * The CIVL function that is the result of this function translator.
	 */
	protected CIVLFunction function;

	/**
	 * The accuracy assumption builder, which performs Taylor expansions after
	 * assumptions involving abstract functions.
	 */
	private AccuracyAssumptionBuilder accuracyAssumptionBuilder;
	
	/**
	 * The current translation is a left hand side expression.
	 */
	private boolean isLHS = false;

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
			Fragment fragment = translateASTNode(node, systemScope, null);

			if (fragment != null)
				initialization = initialization.combineWith(fragment);
		}
		modelFactory.popConditionaExpressionStack();
		if (modelBuilder.mainFunctionNode == null) {
			throw new CIVLSyntaxException("program must have a main function,",
					modelFactory.sourceOf(rootNode));
		}
		this.functionBodyNode = modelBuilder.mainFunctionNode.getBody();
		body = this.translateFunctionBody();
		body = initialization.combineWith(body);
		functionInfo.completeFunction(body);
	}

	/* *************************** Private Methods ************************* */

	/**
	 * Translate the function body node associated with this function
	 * translator.
	 * 
	 * @return The fragment of CIVL locations and statements that represents the
	 *         function body node.
	 */
	protected Fragment translateFunctionBody() {
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
		case ASSUME:
			result = translateAssumeNode(scope, (AssumeNode) statementNode);
			break;
		case ATOMIC:
			result = translateAtomicNode(scope, (AtomicNode) statementNode);
			break;
		case CHOOSE:
			result = translateChooseNode(scope,
					(ChooseStatementNode) statementNode);
			break;
		case COMPOUND:
			result = translateCompoundStatementNode(scope,
					(CompoundStatementNode) statementNode);
			break;
		case EXPRESSION:
			result = translateExpressionStatementNode(scope,
					((ExpressionStatementNode) statementNode).getExpression());
			break;
		case FOR:
			result = translateForLoopNode(scope, (ForLoopNode) statementNode);
			break;
		case GOTO:
			result = translateGotoNode(scope, (GotoNode) statementNode);
			break;
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
		case RETURN:
			result = translateReturnNode(scope, (ReturnNode) statementNode);
			break;
		case SWITCH:
			result = translateSwitchNode(scope, (SwitchNode) statementNode);
			break;
		case WAIT:
			result = translateWaitNode(scope, (WaitNode) statementNode);
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
					result.lastStatement(), result.startLocation());
		}
		modelFactory.popConditionaExpressionStack();
		if (!modelFactory.anonFragment().isEmpty()) {
			result = modelFactory.anonFragment().combineWith(result);
			modelFactory.resetAnonFragment();
		}
		return result;
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

		if (type.isArrayType()) {
			CIVLSource source = array.getSource();
			CIVLArrayType arrayType = (CIVLArrayType) type;
			CIVLType elementType = arrayType.elementType();
			Expression zero = modelFactory.integerLiteralExpression(source,
					BigInteger.ZERO);
			LHSExpression subscript = modelFactory.subscriptExpression(source,
					(LHSExpression) array, zero);
			Expression pointer = modelFactory.addressOfExpression(source,
					subscript);
			Scope scope = array.expressionScope();

			zero.setExpressionScope(scope);
			subscript.setExpressionScope(scope);
			pointer.setExpressionScope(scope);
			((CommonExpression) zero).setExpressionType(modelFactory
					.integerType());
			((CommonExpression) subscript).setExpressionType(elementType);
			((CommonExpression) pointer).setExpressionType(modelFactory
					.pointerType(elementType));
			return pointer;
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
	 * @param scope
	 *            The scope containing this assignment.
	 * @return The model representation of the assignment, which might also be a
	 *         fork statement or function call.
	 */
	private Statement assignStatement(CIVLSource source, LHSExpression lhs,
			ExpressionNode rhsNode, Scope scope) {
		Statement result = null;
		Location location;

		if (isCompleteMallocExpression(rhsNode)) {
			location = modelFactory.location(lhs.getSource(), scope);
			result = mallocStatement(source, location, lhs, (CastNode) rhsNode,
					scope);
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
			result = translateFunctionCall(scope, lhs, functionCallNode, isCall);
		} else {
			Expression rhs;

			modelFactory.setCurrentScope(scope);
			rhs = arrayToPointer(translateExpressionNode(rhsNode, scope, true));
			location = modelFactory.location(lhs.getSource(), scope);
			result = modelFactory.assignStatement(source, location, lhs, rhs,
					false);
		}
		return result;
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
	protected CallOrSpawnStatement callOrSpawnStatement(Scope scope,
			Location location, FunctionCallNode callNode, LHSExpression lhs,
			ArrayList<Expression> arguments, boolean isCall) {
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
				result = modelFactory.callOrSpawnStatement(
						modelFactory.sourceOf(callNode), location, isCall,
						arguments, null);
				break;
			case VARIABLE:
				Expression function = this.translateExpressionNode(
						functionExpression, scope, true);
				callee = null;

				result = modelFactory.callOrSpawnStatement(
						modelFactory.sourceOf(callNode), location, isCall,
						function, arguments, null);
				// added function guard expression since the function could be a
				// system function which has an outstanding guard
				result.setGuard(modelFactory.functionGuardExpression(
						modelFactory.sourceOf(callNode), function, arguments));
				break;
			default:
				throw new CIVLUnimplementedFeatureException(
						"Function call must use identifier of variables or functions for now: "
								+ functionExpression.getSource());
			}
		} else
			throw new CIVLUnimplementedFeatureException(
					"Function call must use identifier for now: "
							+ functionExpression.getSource());

		result.setLhs(lhs);
		if (callee != null)
			modelBuilder.callStatements.put(result, callee);
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
		Set<Statement> continues, breaks;
		Fragment beforeCondition, loopEntrance, loopBody, incrementer = null, loopExit, result;
		Location loopEntranceLocation, continueLocation;
		Pair<Fragment, Expression> refineConditional;

		modelFactory.setCurrentScope(loopScope);
		condition = translateExpressionNode(conditionNode, loopScope, true);
		refineConditional = modelFactory.refineConditionalExpression(loopScope,
				condition, conditionNode);
		beforeCondition = refineConditional.left;
		condition = refineConditional.right;
		condition = modelFactory.booleanExpression(condition);
		loopEntranceLocation = modelFactory.location(
				modelFactory.sourceOf(conditionNode.getSource()), loopScope);
		loopEntrance = new CommonFragment(loopEntranceLocation,
				modelFactory.loopBranchStatement(
						modelFactory.sourceOf(conditionNode.getSource()),
						loopEntranceLocation, condition, true));
		if (beforeCondition != null) {
			loopEntrance = beforeCondition.combineWith(loopEntrance);
		}
		functionInfo.addContinueSet(new LinkedHashSet<Statement>());
		functionInfo.addBreakSet(new LinkedHashSet<Statement>());
		loopBody = translateStatementNode(loopScope, loopBodyNode);
		continues = functionInfo.popContinueStack();
		// if there is no incrementer statement, continue statements will go to
		// the loop entrance/exit location
		if (incrementerNode != null) {
			incrementer = translateExpressionStatementNode(loopScope,
					incrementerNode);
			continueLocation = incrementer.startLocation();
		} else
			continueLocation = loopEntrance.startLocation();
		for (Statement s : continues) {
			s.setTarget(continueLocation);
		}
		loopEntrance.startLocation().setLoopPossible(true);
		// the loop entrance location is the same as the loop exit location
		loopExit = new CommonFragment(modelFactory.loopBranchStatement(
				condition.getSource(), loopEntranceLocation, modelFactory
						.unaryExpression(condition.getSource(),
								UNARY_OPERATOR.NOT, condition), false));
		// incrementer comes after the loop body
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
		if (breaks.size() > 0) {
			// The set of all statements that exit the loop. This is the loop
			// exit statement, plus any breaks. All of these statements will be
			// set to the same target later when this fragment is combined with
			// the next fragment.
			StatementSet lastStatements = new StatementSet();

			lastStatements.add(loopExit.lastStatement());
			for (Statement s : breaks) {
				lastStatements.add(s);
			}
			result.setLastStatement(lastStatements);
		} else {
			result.setLastStatement(loopExit.lastStatement());
		}
		return result;
	}

	// how to process individual block elements?
	// int x: INTEGER or STRING -> universe.integer
	// real x: INTEGER or DOUBLE or STRING -> universe.real
	// String x: STRING
	// boolean x : BOOLEAN
	// else no can do yet
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
			case STRING:
				throw new CIVLUnimplementedFeatureException("Strings");
			default:
			}
		}
		throw new CIVLUnimplementedFeatureException(
				"Specification of initial value not of integer, real, or boolean type",
				variable);
	}

	/**
	 * Checks if a given fragment (which is to be used as the function body of
	 * some function) contains a return statement.
	 * 
	 * @param functionBody
	 *            The fragment to be checked.
	 * @return True iff a return statement can be reached back from the last
	 *         statement.
	 */
	private boolean containsReturn(Fragment functionBody) {
		if (functionBody == null || functionBody.isEmpty())
			return false;
		if (functionBody.lastStatement() instanceof ReturnStatement)
			return true;
		if (functionBody.lastStatement() instanceof StatementSet) {
			StatementSet lastStatements = (StatementSet) functionBody
					.lastStatement();

			for (Statement statement : lastStatements.statements()) {
				if (!(statement instanceof ReturnStatement))
					return false;
			}
			return true;
		}
		if (functionBody.lastStatement().source().getNumOutgoing() == 1) {
			Location lastLocation = functionBody.lastStatement().source();
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
	 * 
	 * @return True when there are incomplete $atom blocks being translating,
	 *         i.e, when the number of active $atom blocks is greater than 0.
	 */
	private boolean inAtom() {
		return atomCount > 0;
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
		modelFactory.setCurrentScope(scope);
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
		Statement assignStatement;

		modelFactory.setCurrentScope(scope);
		this.isLHS = true;
		leftExpression = translateExpressionNode(lhs, scope, true);
		this.isLHS = false;
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
		assignStatement = assignStatement(modelFactory.sourceOfSpan(lhs, rhs),
				(LHSExpression) leftExpression, rhs, scope);
		return new CommonFragment(assignStatement);
	}

	/**
	 * Translate an assume node into a fragment of CIVL statements
	 * 
	 * @param scope
	 *            The scope containing this statement.
	 * @param assumeNode
	 *            The scope containing this statement.
	 * @return the fragment
	 */
	private Fragment translateAssumeNode(Scope scope, AssumeNode assumeNode) {
		Expression expression;
		Location location;
		Fragment result;

		modelFactory.setCurrentScope(scope);
		expression = translateExpressionNode(assumeNode.getExpression(), scope,
				true);
		location = modelFactory.location(
				modelFactory.sourceOfBeginning(assumeNode), scope);
		result = modelFactory.assumeFragment(modelFactory.sourceOf(assumeNode),
				location, expression);
		result = result.combineWith(accuracyAssumptionBuilder
				.accuracyAssumptions(expression, scope));
		return result;
	}

	/**
	 * @param node
	 *            The AST node
	 * @param scope
	 *            The scope
	 * @param location
	 *            The location
	 * @return The fragment of statements translated from the AST node
	 */
	protected Fragment translateASTNode(ASTNode node, Scope scope,
			Location location) {
		Fragment result = null;

		switch (node.nodeKind()) {
		case VARIABLE_DECLARATION:
			try {
				result = translateVariableDeclarationNode(location, scope,
						(VariableDeclarationNode) node);
			} catch (CommandLineException e) {
				throw new CIVLInternalException(
						"Saw input variable outside of root scope",
						modelFactory.sourceOf(node));
			}
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
		case SCOPE_PARAMETERIZED_DECLARATION:
			result = translateScopeParameterizedDeclarationNode(scope,
					(ScopeParameterizedDeclarationNode) node);
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
		Iterator<Enumerator> enumerators = enumType.getEnumerators();
		int numOfEnumerators = enumType.getNumEnumerators();
		BigInteger currentValue = BigInteger.ZERO;
		Map<String, BigInteger> valueMap = new LinkedHashMap<>(numOfEnumerators);

		if (name == null) {
			name = "__enum_";
		}
		while (enumerators.hasNext()) {
			Enumerator enumerator = enumerators.next();
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
		return modelFactory.enumType(name, valueMap);
	}

	private Fragment translateScopeParameterizedDeclarationNode(Scope scope,
			ScopeParameterizedDeclarationNode scopedNode) {
		SequenceNode<VariableDeclarationNode> parameters = scopedNode
				.parameters();
		ArrayList<Variable> scopeParameters = new ArrayList<>();
		int numOfParameters = parameters.numChildren();
		DeclarationNode baseDeclarationNode = scopedNode.baseDeclaration();

		if (baseDeclarationNode instanceof FunctionDeclarationNode) {
			for (int i = 0; i < numOfParameters; i++) {
				VariableDeclarationNode decl = parameters.getSequenceChild(i);
				CIVLSource source = modelFactory.sourceOf(decl.getIdentifier());
				Identifier variableName = modelFactory.identifier(source,
						decl.getName());

				scopeParameters.add(modelFactory.variable(source,
						modelFactory.scopeType(), variableName,
						scopeParameters.size()));
			}
			translateFunctionDeclarationNode(
					(FunctionDeclarationNode) baseDeclarationNode, scope,
					scopeParameters);
		}
		return null;
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

		if (atomicNode.isAtom())
			this.atomCount++;
		bodyFragment = translateStatementNode(scope, bodyNode);
		if (atomicNode.isAtom())
			this.atomCount--;
		bodyFragment = modelFactory.atomicFragment(atomicNode.isAtom(),
				bodyFragment, start, end);
		return bodyFragment;
	}

	/**
	 * Translate a function call of the function $choose_int into a choose
	 * statement. An syntax exception will be thrown if this $choose_int
	 * function call is found to be within an $atom block.
	 * 
	 * @param source
	 *            The CIVL source of the function call.
	 * @param location
	 *            The location of the function call.
	 * @param scope
	 *            The scope of this function call.
	 * @param lhs
	 *            The left hand side expression
	 * @param arguments
	 *            The list of arguments for choose_int function call. The number
	 *            of arguments should be exactly one, otherwise an exception
	 *            will be thrown.
	 * @return The new choose statement.
	 */
	private Statement translateChooseIntFunctionCall(CIVLSource source,
			Location location, Scope scope, LHSExpression lhs,
			ArrayList<Expression> arguments) {
		int numberOfArgs = arguments.size();

		if (this.inAtom()) {
			throw new CIVLSyntaxException(
					"The non-deterministic function $choose_int is not allowed in $atom block.",
					source);
		}
		if (numberOfArgs != 1) {
			throw new CIVLSyntaxException(
					"The function $choose_int should have exactly one argument.",
					source);
		}
		return modelFactory.chooseStatement(source, location, lhs,
				arguments.get(0));
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
		Location startLocation = modelFactory.location(
				modelFactory.sourceOfBeginning(chooseStatementNode), scope);
		int defaultOffset = 0;
		Fragment result = new CommonFragment();
		Iterator<Statement> iter;
		Expression defaultGuard = null;

		if (chooseStatementNode.getDefaultCase() != null) {
			defaultOffset = 1;
		}
		for (int i = 0; i < chooseStatementNode.numChildren() - defaultOffset; i++) {
			StatementNode childNode = chooseStatementNode.getSequenceChild(i);
			Fragment caseFragment = translateStatementNode(scope, childNode);

			// make all case fragment to start at the same location
			caseFragment.updateStartLocation(startLocation);
			// combine all case fragments as branches of the start location
			result = result.parallelCombineWith(caseFragment);
		}
		iter = startLocation.outgoing().iterator();
		// Compute the guard for the default statement
		while (iter.hasNext()) {
			Expression statementGuard = iter.next().guard();

			if (defaultGuard == null)
				defaultGuard = statementGuard;
			else if (modelFactory.isTrue(defaultGuard)) {
				defaultGuard = statementGuard;
			} else if (modelFactory.isTrue(statementGuard)) {
				// Keep current guard
			} else {
				defaultGuard = modelFactory.binaryExpression(modelFactory
						.sourceOfSpan(defaultGuard.getSource(),
								statementGuard.getSource()),
						BINARY_OPERATOR.OR, defaultGuard, statementGuard);
			}
		}
		defaultGuard = modelFactory.unaryExpression(defaultGuard.getSource(),
				UNARY_OPERATOR.NOT, defaultGuard);
		if (chooseStatementNode.getDefaultCase() != null) {
			Fragment defaultFragment = translateStatementNode(scope,
					chooseStatementNode.getDefaultCase());

			// update the guard of the first statements in defaultFragment to be
			// the conjunction of the defaultGuard and the statement's guard
			defaultFragment.addGuardToStartLocation(defaultGuard, modelFactory);
			// update the start location of default fragment
			defaultFragment.updateStartLocation(startLocation);
			// combine the default fragment as a branch of the start location
			result = result.parallelCombineWith(defaultFragment);
		}
		return result;
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
		boolean newScopeNeeded = false;

		// In order to eliminate unnecessary scopes, do this loop twice.
		// The first time, just check if there are any declarations. If there
		// are, create newScope as usual. Otherwise, let newScope = scope.
		for (int i = 0; i < statementNode.numChildren(); i++) {
			BlockItemNode node = statementNode.getSequenceChild(i);

			if (node instanceof VariableDeclarationNode) {
				newScopeNeeded = true;
				break;
			}
			if (node instanceof LabeledStatementNode) {
				StatementNode labeledStatementNode = ((LabeledStatementNode) node)
						.getStatement();
				if (labeledStatementNode instanceof VariableDeclarationNode) {
					newScopeNeeded = true;
					break;
				}
			}
		}
		if (!newScopeNeeded) {
			newScopeNeeded = hasHereNode(statementNode.getScope(),
					statementNode);
		}
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
	 * @param scope
	 *            The scope to be checked.
	 * @param astNode
	 *            The AST node to be checked.
	 * @return True iff a $here node exists in the AST node and is in the given
	 *         scope.
	 */
	private boolean hasHereNode(edu.udel.cis.vsl.abc.ast.entity.IF.Scope scope,
			ASTNode astNode) {
		int number = astNode.numChildren();

		if (number < 1)
			return false;
		for (int i = 0; i < number; i++) {
			ASTNode child = astNode.child(i);

			if (child == null)
				continue;
			if (!child.getScope().equals(scope))
				continue;
			else {
				if (child instanceof HereOrRootNode) {
					if (((HereOrRootNode) child).isHereNode())
						return true;
				} else {
					boolean result = hasHereNode(scope, child);

					if (result)
						return result;
				}
			}
		}
		return false;
	}

	/**
	 * Takes an expression statement and converts it to a fragment of that
	 * statement. Currently supported expressions for expression statements are
	 * spawn, assign, function call, increment, decrement. Any other expressions
	 * have no side effects and thus result in a no-op.
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
		case OPERATOR:
			OperatorNode operatorNode = (OperatorNode) expressionNode;

			switch (operatorNode.getOperator()) {
			case ASSIGN:
				result = translateAssignNode(scope, operatorNode);
				break;
			case POSTINCREMENT:
			case PREINCREMENT:
			case POSTDECREMENT:
			case PREDECREMENT:
				throw new CIVLInternalException("Side-effect not removed: ",
						modelFactory.sourceOf(operatorNode));
			default:
				// since side-effects have been removed,
				// the only expressions remaining with side-effects
				// are assignments. all others are equivalent to no-op
				Statement noopStatement = modelFactory.noopStatement(
						modelFactory.sourceOf(operatorNode), location);

				result = new CommonFragment(noopStatement);
			}
			break;
		case SPAWN:
			result = translateSpawnNode(scope, (SpawnNode) expressionNode);
			break;
		case FUNCTION_CALL:
			result = translateFunctionCallNode(scope,
					(FunctionCallNode) expressionNode);
			break;
		default:
			throw new CIVLUnimplementedFeatureException(
					"expression statement of this kind",
					modelFactory.sourceOf(expressionNode));
		}
		return result;
	}

	/**
	 * Translate a for loop node into a fragment
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
		Scope newScope = scope;
		Fragment result;
		Location location;

		// If the initNode does not have a declaration, don't create a new
		// scope.
		if (initNode != null) {
			switch (initNode.nodeKind()) {
			case EXPRESSION:
				location = modelFactory.location(
						modelFactory.sourceOfBeginning(forLoopNode), newScope);
				initFragment = translateExpressionStatementNode(newScope,
						(ExpressionNode) initNode);
				break;
			case DECLARATION_LIST:
				newScope = modelFactory.scope(
						modelFactory.sourceOf(forLoopNode), scope,
						new LinkedHashSet<Variable>(), functionInfo.function());
				for (int i = 0; i < ((DeclarationListNode) initNode)
						.numChildren(); i++) {
					VariableDeclarationNode declaration = ((DeclarationListNode) initNode)
							.getSequenceChild(i);
					Variable variable = translateVariableDeclarationNode(
							declaration, newScope);
					Fragment fragment;

					location = modelFactory.location(
							modelFactory.sourceOfBeginning(forLoopNode),
							newScope);
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
		}
		result = composeLoopFragment(newScope, forLoopNode.getCondition(),
				forLoopNode.getBody(), forLoopNode.getIncrementer(), false);
		result = initFragment.combineWith(result);
		return result;
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
	protected Statement translateFunctionCall(Scope scope, LHSExpression lhs,
			FunctionCallNode functionCallNode, boolean isCall) {
		CIVLSource source = modelFactory.sourceOfBeginning(functionCallNode);
		String functionName = ((IdentifierExpressionNode) functionCallNode
				.getFunction()).getIdentifier().name();
		ArrayList<Expression> arguments = new ArrayList<Expression>();
		Location location;
		CIVLFunction abstractFunction;
		Function callee;
		ExpressionNode functionExpression = functionCallNode.getFunction();

		if (functionExpression instanceof IdentifierExpressionNode) {
			Entity entity = ((IdentifierExpressionNode) functionExpression)
					.getIdentifier().getEntity();

			if (entity.getEntityKind() == EntityKind.FUNCTION) {
				callee = (Function) entity;
				abstractFunction = modelBuilder.functionMap.get(callee);
			} else
				abstractFunction = null;
		} else
			throw new CIVLUnimplementedFeatureException(
					"Function call must use identifier for now: "
							+ functionExpression.getSource());
		modelFactory.setCurrentScope(scope);
		for (int i = 0; i < functionCallNode.getNumberOfArguments(); i++) {
			Expression actual = translateExpressionNode(
					functionCallNode.getArgument(i), scope, true);

			actual = arrayToPointer(actual);
			arguments.add(actual);
		}
		location = modelFactory.location(
				modelFactory.sourceOfBeginning(functionCallNode), scope);
		if (abstractFunction != null
				&& abstractFunction instanceof AbstractFunction) {
			Expression abstractFunctionCall = modelFactory
					.abstractFunctionCallExpression(
							modelFactory.sourceOf(functionCallNode),
							(AbstractFunction) abstractFunction, arguments);

			return modelFactory.assignStatement(source, location, lhs,
					abstractFunctionCall, false);
		}
		switch (functionName) {
		// special translation for some system functions like $assert,
		// $choose_int, etc.
		case "assert":
		case "$assert":
			return translateAssertFunctionCall(source, location, scope,
					arguments);
		case "$choose_int":
			return translateChooseIntFunctionCall(source, location, scope, lhs,
					arguments);
		default:
			return callOrSpawnStatement(scope, location, functionCallNode, lhs,
					arguments, isCall);
		}
	}

	/**
	 * Translate the function call $assert() (from civlc.h) or assert() (from
	 * assert.h) into an Assert Statement.
	 * 
	 * @param source
	 *            The source code element for error report.
	 * @param location
	 *            The source location of the function call.
	 * @param scope
	 *            The scope where the function call happens.
	 * @param arguments
	 *            The arguments of the function call.
	 * @return A new assert statement representing the $assert/assert function
	 *         call.
	 */
	private Statement translateAssertFunctionCall(CIVLSource source,
			Location location, Scope scope, ArrayList<Expression> arguments) {
		Statement result;

		switch (arguments.size()) {
		case 0:
			throw new CIVLSyntaxException(
					"The function $assert should have at least one arguments.",
					source);
		case 1:
			result = modelFactory.assertStatement(source, location,
					modelFactory.booleanExpression(arguments.get(0)));
			break;
		default:
			ArrayList<Expression> optionalArguments = new ArrayList<>();

			for (int i = 1; i < arguments.size(); i++) {
				optionalArguments.add(arguments.get(i));
			}

			result = modelFactory.assertStatement(source, location,
					modelFactory.booleanExpression(arguments.get(0)),
					optionalArguments);
		}
		return result;
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
			FunctionCallNode functionCallNode) {
		Statement functionCall = translateFunctionCall(scope, null,
				functionCallNode, true);

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
				&& (!(node instanceof CommonFunctionDefinitionNode)))
			return;
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
				CIVLType type = translateABCType(modelFactory.sourceOf(decl),
						scope, functionType.getParameterType(i));
				CIVLSource source = modelFactory.sourceOf(decl.getIdentifier());
				Identifier variableName = modelFactory.identifier(source,
						decl.getName());

				parameters.add(modelFactory.variable(source, type,
						variableName, parameters.size()));
			}
			if (entity.getDefinition() == null) { // abstract or system function
				if (node instanceof AbstractFunctionDefinitionNode) {
					result = modelFactory.abstractFunction(nodeSource,
							functionIdentifier, parameters, returnType, scope,
							((AbstractFunctionDefinitionNode) node)
									.continuity());
				} else {
					Source declSource = node.getIdentifier().getSource();
					CToken token = declSource.getFirstToken();
					File file = token.getSourceFile();
					String fileName = file.getName(); // fileName will be
														// something
														// like "stdlib.h" or
														// "civlc.h"
					String libName;

					if (!fileName.contains("."))
						throw new CIVLInternalException("Malformed file name "
								+ fileName + " containing system function "
								+ functionName, nodeSource);

					libName = fileNameWithoutExtension(fileName);
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
		// result is now defined and in the model
		if (contract != null) {
			Expression precondition = result.precondition();
			Expression postcondition = result.postcondition();

			modelFactory.setCurrentScope(scope);
			for (int i = 0; i < contract.numChildren(); i++) {
				ContractNode contractComponent = contract.getSequenceChild(i);
				Expression componentExpression;

				if (contractComponent instanceof EnsuresNode) {
					componentExpression = translateExpressionNode(
							((EnsuresNode) contractComponent).getExpression(),
							result.outerScope(), true);
					if (postcondition == null) {
						postcondition = componentExpression;
					} else {
						postcondition = modelFactory.binaryExpression(
								modelFactory.sourceOfSpan(
										postcondition.getSource(),
										componentExpression.getSource()),
								BINARY_OPERATOR.AND, postcondition,
								componentExpression);
					}
				} else {
					componentExpression = translateExpressionNode(
							((RequiresNode) contractComponent).getExpression(),
							result.outerScope(), true);
					if (precondition == null) {
						precondition = componentExpression;
					} else {
						precondition = modelFactory.binaryExpression(
								modelFactory.sourceOfSpan(
										precondition.getSource(),
										componentExpression.getSource()),
								BINARY_OPERATOR.AND, precondition,
								componentExpression);
					}
				}
			}
			if (precondition != null)
				result.setPrecondition(precondition);
			if (postcondition != null)
				result.setPostcondition(postcondition);
		}
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
		functionInfo.putToGotoStatements(noop, label);
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
				.refineConditionalExpression(scope, expression, conditionNode);

		beforeCondition = refineConditional.left;
		expression = refineConditional.right;
		expression = modelFactory.booleanExpression(expression);
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
		if (beforeCondition != null) {
			result = beforeCondition.combineWith(result);
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
				modelFactory.sourceOf(jumpNode), location);

		if (jumpNode.getKind() == JumpKind.CONTINUE) {
			functionInfo.peekContinueStack().add(result);
		} else if (jumpNode.getKind() == JumpKind.BREAK) {
			functionInfo.peekBreakStack().add(result);
		} else {
			throw new CIVLInternalException(
					"Jump nodes other than BREAK and CONTINUE should be handled seperately.",
					modelFactory.sourceOf(jumpNode.getSource()));
		}
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
		switch (loopNode.getKind()) {
		case WHILE:
			return composeLoopFragment(scope, loopNode.getCondition(),
					loopNode.getBody(), null, false);
		case DO_WHILE:
			return composeLoopFragment(scope, loopNode.getCondition(),
					loopNode.getBody(), null, true);
		default:
			throw new CIVLInternalException("Unreachable",
					modelFactory.sourceOf(loopNode));
		}
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
				modelFactory.sourceOf(nullStatementNode), location));
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
		Location location = modelFactory.location(
				modelFactory.sourceOfBeginning(returnNode), scope);
		Expression expression;
		CIVLFunction function = this.functionInfo.function();

		if (returnNode.getExpression() != null) {
			expression = translateExpressionNode(returnNode.getExpression(),
					scope, true);
			if (function.returnType().isBoolType())
				expression = modelFactory.booleanExpression(expression);
		} else
			expression = null;
		return modelFactory.returnFragment(modelFactory.sourceOf(returnNode),
				location, expression, function);
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
				spawnNode.getCall(), false));
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
			functionInfo.putToGotoStatements(caseGoto.lastStatement(), label);
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
			functionInfo
					.putToGotoStatements(defaultGoto.lastStatement(), label);
		} else {
			defaultExit = modelFactory.noopStatement(modelFactory
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
				result.addLastStatement(s);
			}
		}
		if (defaultExit != null)
			result.addLastStatement(defaultExit);
		return result;
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
		CIVLType type = variable.type();
		Fragment result = null, initialization = null;
		IdentifierNode identifier = node.getIdentifier();
		CIVLSource source = modelFactory.sourceOf(node);

		if (variable.isInput() || type instanceof CIVLArrayType
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
				result = new CommonFragment(sourceLocation,
						modelFactory.assignStatement(source, sourceLocation,
								modelFactory.variableExpression(
										modelFactory.sourceOf(identifier),
										variable), rhs, true));
				sourceLocation = null;
			}
		}
		initialization = translateVariableInitializationNode(node, variable,
				sourceLocation, scope);
		if (result == null)
			result = initialization;
		else
			result = result.combineWith(initialization);
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
		}
		if (node.getTypeNode().isOutputQualified()) {
			variable.setIsOutput(true);
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

		modelFactory.setCurrentScope(scope);
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
				rhs = translateExpressionNode((ExpressionNode) init, scope,
						true);
				if (rhs instanceof SystemFunctionCallExpression) {
					CallOrSpawnStatement callStatement = ((SystemFunctionCallExpression) rhs)
							.callStatement();

					callStatement.setLhs(modelFactory.variableExpression(
							modelFactory.sourceOf(init), variable));
					return new CommonFragment(callStatement);
				} else if (init instanceof CompoundLiteralNode) {
					CIVLType variableType = variable.type();

					if (variableType.isPointerType()) {
						Variable anonVariable = modelFactory
								.newAnonymousVariableForArrayLiteral(
										initSource, scope,
										(CIVLArrayType) rhs.getExpressionType());

						anonStatement = modelFactory.assignStatement(
								initSource, modelFactory.location(initSource,
										scope), modelFactory
										.variableExpression(initSource,
												anonVariable), rhs, true);
						rhs = arrayToPointer(modelFactory.variableExpression(
								initSource, anonVariable));
					}
				}
			} else {
				CIVLType variableType = variable.type();

				rhs = translateCompoundLiteralObject(
						((CompoundInitializerNode) init).getLiteralObject(),
						scope, variableType);
				if (variableType.isPointerType()) {
					Variable anonVariable = modelFactory
							.newAnonymousVariableForArrayLiteral(initSource,
									scope,
									(CIVLArrayType) rhs.getExpressionType());

					anonStatement = modelFactory.assignStatement(initSource,
							modelFactory.location(initSource, scope),
							modelFactory.variableExpression(initSource,
									anonVariable), rhs, true);
					rhs = arrayToPointer(modelFactory.variableExpression(
							initSource, anonVariable));
				}
			}
			assignStatement = modelFactory.assignStatement(modelFactory
					.sourceOf(node), location, modelFactory.variableExpression(
					modelFactory.sourceOf(init), variable), rhs, true);
			initFragment = new CommonFragment(assignStatement);
			if (anonStatement != null) {
				initFragment = new CommonFragment(anonStatement)
						.combineWith(initFragment);
			}
			if (!modelFactory.anonFragment().isEmpty()) {
				initFragment = modelFactory.anonFragment().combineWith(
						initFragment);
				modelFactory.resetAnonFragment();
			}
			if (modelFactory.hasConditionalExpressions()) {
				initFragment = modelFactory
						.refineConditionalExpressionOfStatement(
								assignStatement, location);
			}
		}
		return initFragment;
	}

	private Expression translateCompoundLiteralNode(
			CompoundLiteralNode compoundNode, Scope scope) {
		CIVLType type = translateABCType(
				modelFactory.sourceOf(compoundNode.getTypeNode()), scope,
				compoundNode.getType());

		return translateCompoundLiteralObject(compoundNode.getInitializerList()
				.getLiteralObject(), scope, type);
	}

	private Expression translateCompoundLiteralObject(
			CompoundLiteralObject compoundLiteral, Scope scope, CIVLType type) {
		ASTNode node = compoundLiteral.getSourceNode();
		CIVLSource source = modelFactory.sourceOf(node);
		int compoundLiteralSize = compoundLiteral.size();

		if (type.isArrayType() || type.isPointerType()) {
			CIVLArrayType arrayType;
			ArrayList<Expression> elements = new ArrayList<>();

			if (type.isPointerType()) {
				arrayType = modelFactory.completeArrayType(
						((CIVLPointerType) type).baseType(),
						modelFactory.integerLiteralExpression(null,
								BigInteger.valueOf(compoundLiteralSize)));
			} else
				arrayType = (CIVLArrayType) type;
			for (int i = 0; i < compoundLiteralSize; i++) {
				LiteralObject literal = compoundLiteral.get(i);
				Expression element;

				if (literal instanceof ScalarLiteralObject) {
					element = translateExpressionNode(
							((ScalarLiteralObject) literal).getExpression(),
							scope, true);
				} else if (literal instanceof CompoundLiteralObject) {
					element = translateCompoundLiteralObject(
							((CompoundLiteralObject) literal), scope,
							arrayType.elementType());
				} else
					throw new CIVLInternalException("Unreachable", source);
				elements.add(element);
			}
			return modelFactory.arrayLiteralExpression(source, arrayType,
					elements);
		} else if (type.isStructType() || type.isUnionType()) {
			CIVLStructOrUnionType structType = (CIVLStructOrUnionType) type;
			ArrayList<Expression> fields = new ArrayList<>();

			for (int i = 0; i < compoundLiteralSize; i++) {
				LiteralObject literal = compoundLiteral.get(i);
				Expression field;
				CIVLType fieldType = structType.getField(i).type();

				if (literal instanceof ScalarLiteralObject) {
					field = translateExpressionNode(
							((ScalarLiteralObject) literal).getExpression(),
							scope, true);
				} else if (literal instanceof CompoundLiteralObject) {
					field = translateCompoundLiteralObject(
							((CompoundLiteralObject) literal), scope, fieldType);
				} else
					throw new CIVLInternalException("Unreachable", source);
				fields.add(field);
			}
			return modelFactory.structOrUnionLiteralExpression(source,
					structType, fields);
		} else
			throw new CIVLInternalException("Compound initializer of " + type
					+ " type is invalid.", source);
	}

	/**
	 * Translate a Wait node to a fragment of a CIVL join statement
	 * 
	 * @param scope
	 *            The scope
	 * @param waitNode
	 *            The wait node
	 * @return the fragment of the wait statement
	 */
	private Fragment translateWaitNode(Scope scope, WaitNode waitNode) {
		CIVLSource source = modelFactory.sourceOf(waitNode);
		Location location = modelFactory.location(
				modelFactory.sourceOfBeginning(waitNode), scope);

		if (inAtom()) {
			throw new CIVLSyntaxException(
					"$wait statement is not allowed in $atom blocks,", source);
		}
		return modelFactory.joinFragment(source, location,
				translateExpressionNode(waitNode.getExpression(), scope, true));
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
				.refineConditionalExpression(scope, whenGuard, whenGuardNode);
		Fragment beforeGuardFragment = refineConditional.left, result;

		whenGuard = refineConditional.right;
		whenGuard = modelFactory.booleanExpression(whenGuard);
		result = translateStatementNode(scope, whenNode.getBody());
		if (!modelFactory.isTrue(whenGuard)) {
			// Each outgoing statement from the first location in this
			// fragment should have its guard set to the conjunction of guard
			// and that statement's guard.
			result.addGuardToStartLocation(whenGuard, modelFactory);
		}
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

		modelFactory.setCurrentScope(scope);
		castExpression = translateExpressionNode(argumentNode, scope, true);
		if (castType.isPointerType()
				&& !castExpression.getExpressionType().isPointerType()
				&& castExpression instanceof LHSExpression) {
			result = modelFactory.castExpression(source, castType,
					modelFactory.addressOfExpression(source,
							(LHSExpression) castExpression));
		} else
			result = modelFactory.castExpression(source, castType,
					castExpression);
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
	private Expression translateConstantNode(ConstantNode constantNode) {
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
			assert constantNode.getStringRepresentation().equals("$self");
			result = modelFactory.selfExpression(source);
			break;
		case OTHER_INTEGER:
			if (constantNode instanceof EnumerationConstantNode) {
				BigInteger value = ((IntegerValue) ((EnumerationConstantNode) constantNode)
						.getConstantValue()).getIntegerValue();

				result = modelFactory.integerLiteralExpression(source, value);
			} else
				result = modelFactory.integerLiteralExpression(source,
						BigInteger.valueOf(Long.parseLong(constantNode
								.getStringRepresentation())));
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
				} else
					result = modelFactory.integerLiteralExpression(source,
							BigInteger.valueOf(Long.parseLong(constantNode
									.getStringRepresentation())));
				break;
			case FLOAT:
			case DOUBLE:
			case LONG_DOUBLE:
				result = modelFactory.realLiteralExpression(source, BigDecimal
						.valueOf(Double.parseDouble(constantNode
								.getStringRepresentation())));
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
				result = modelFactory.charLiteralExpression(source,
						constantNode.getStringRepresentation().charAt(1));
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
			boolean isSupportedChar = false;

			if (constantNode.getStringRepresentation().equals("0")) {
				result = modelFactory.nullPointerExpression(
						modelFactory.pointerType(modelFactory.voidType()),
						source);
				break;
			} else if (constantNode instanceof StringLiteralNode) {
				if (((PointerType) convertedType).referencedType().kind() == TypeKind.BASIC
						&& ((StandardBasicType) ((PointerType) convertedType)
								.referencedType()).getBasicTypeKind() == BasicTypeKind.CHAR) {
					isSupportedChar = true;
				} else if (((PointerType) convertedType).referencedType()
						.kind() == TypeKind.QUALIFIED
						&& ((QualifiedObjectType) ((PointerType) convertedType)
								.referencedType()).getBaseType() instanceof CommonCharType) {
					isSupportedChar = true;
				}
				if (isSupportedChar) {
					StringLiteralNode stringLiteralNode = (StringLiteralNode) constantNode;
					StringLiteral stringValue = stringLiteralNode
							.getConstantValue().getLiteral();
					CIVLArrayType arrayType = modelFactory.completeArrayType(
							modelFactory.charType(), modelFactory
									.integerLiteralExpression(source,
											BigInteger.valueOf(stringValue
													.getNumCharacters())));
					ArrayList<Expression> chars = new ArrayList<>();
					ArrayLiteralExpression stringLiteral;
					VariableExpression anonVariable = modelFactory
							.variableExpression(source, modelFactory
									.newAnonymousVariableForArrayLiteral(
											source,
											modelFactory.currentScope(),
											arrayType));
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
					anonAssign = modelFactory.assignStatement(
							source,
							modelFactory.location(source,
									modelFactory.currentScope()), anonVariable,
							stringLiteral, true);
					modelFactory.addAnonStatement(anonAssign);
					result = arrayToPointer(anonVariable);
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
			result = translateConstantNode((ConstantNode) expressionNode);
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
		case RESULT:
			result = modelFactory.resultExpression(modelFactory
					.sourceOf(expressionNode));
			break;
		case SCOPEOF:
			result = translateScopeofNode((ScopeOfNode) expressionNode, scope);
			break;
		case SELF:
			result = modelFactory.selfExpression(modelFactory
					.sourceOf(expressionNode));
			break;
		case SIZEOF:
			result = translateSizeofNode((SizeofNode) expressionNode, scope);
			break;
		default:
			throw new CIVLUnimplementedFeatureException("expressions of type "
					+ expressionNode.getClass().getSimpleName(),
					modelFactory.sourceOf(expressionNode));
		}
		if (translateConversions) {
			// apply conversions
			CIVLSource source = result.getSource();
			int numConversions = expressionNode.getNumConversions();

			for (int i = 0; i < numConversions; i++) {
				Conversion conversion = expressionNode.getConversion(i);
				Type oldType = conversion.getOldType();
				Type newType = conversion.getNewType();
				// Arithmetic, Array, CompatibleStructureOrUnion,
				// Function, Lvalue, NullPointer, PointerBool, VoidPointer

				if (conversion instanceof ArithmeticConversion) {
					CIVLType oldCIVLType = translateABCType(source, scope,
							oldType);
					CIVLType newCIVLType = translateABCType(source, scope,
							newType);

					// need equals on Types
					if (oldCIVLType.isIntegerType()
							&& newCIVLType.isIntegerType()
							|| oldCIVLType.isRealType()
							&& newCIVLType.isRealType()) {
						// nothing to do
					} else {
						// Sometimes the conversion might have been done during
						// the translating the expression node, for example,
						// when translating a constant node, so only create a
						// cast expression if necessary.
						if (!result.getExpressionType().equals(newCIVLType))
							result = modelFactory.castExpression(source,
									newCIVLType, result);
					}
				} else if (conversion instanceof CompatiblePointerConversion) {
					// nothing to do
				} else if (conversion instanceof ArrayConversion) {
					// we will ignore this one here because we want
					// to keep it as array in subscript expressions
				} else if (conversion instanceof CompatibleStructureOrUnionConversion) {
					// think about this
					throw new CIVLUnimplementedFeatureException(
							"compatible structure or union conversion", source);
				} else if (conversion instanceof FunctionConversion) {
				} else if (conversion instanceof LvalueConversion) {
					// nothing to do since ignore qualifiers anyway
				} else if (conversion instanceof NullPointerConversion) {
					// result is a null pointer to new type
					CIVLPointerType newCIVLType = (CIVLPointerType) translateABCType(
							source, scope, newType);

					result = modelFactory.nullPointerExpression(newCIVLType,
							source);
				} else if (conversion instanceof PointerBoolConversion) {
					// pointer type to boolean type: p!=NULL
					result = modelFactory.binaryExpression(source,
							BINARY_OPERATOR.NOT_EQUAL, result, modelFactory
									.nullPointerExpression(
											(CIVLPointerType) result
													.getExpressionType(),
											source));
				} else if (conversion instanceof VoidPointerConversion) {
					// void*->T* or T*->void*
					// ignore, pointer types are all the same
					// all pointer types are using the same symbolic object type
				} else
					throw new CIVLInternalException("Unknown conversion: "
							+ conversion, source);
			}
		}
		return result;
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
	private Expression translateFunctionCallExpression(
			FunctionCallNode callNode, Scope scope) {
		Expression result;
		ExpressionNode functionExpression = callNode.getFunction();
		Function callee;
		CIVLFunction abstractFunction;
		List<Expression> arguments = new ArrayList<Expression>();
		CIVLSource source = modelFactory.sourceOf(callNode);

		if (functionExpression instanceof IdentifierExpressionNode) {
			callee = (Function) ((IdentifierExpressionNode) functionExpression)
					.getIdentifier().getEntity();
		} else
			throw new CIVLUnimplementedFeatureException(
					"Function call must use identifier for now: "
							+ functionExpression.getSource());
		abstractFunction = modelBuilder.functionMap.get(callee);
		assert abstractFunction != null;
		if (abstractFunction instanceof AbstractFunction) {
			modelFactory.setCurrentScope(scope);
			for (int i = 0; i < callNode.getNumberOfArguments(); i++) {
				Expression actual = translateExpressionNode(
						callNode.getArgument(i), scope, true);

				actual = arrayToPointer(actual);
				arguments.add(actual);
			}
			result = modelFactory.abstractFunctionCallExpression(
					modelFactory.sourceOf(callNode),
					(AbstractFunction) abstractFunction, arguments);
			return result;
		} else {
			Statement functionCall = this.translateFunctionCall(scope, null,
					callNode, true);

			if (functionCall instanceof CallOrSpawnStatement) {
				CallOrSpawnStatement callStatement = (CallOrSpawnStatement) functionCall;

				return modelFactory.systemFunctionCallExpression(callStatement);
			} else {
				throw new CIVLInternalException("Unreachable", source);
			}
		}
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
			VariableExpression varExpression = modelFactory.variableExpression(source,
					scope.variable(name));
			
			if(!this.isLHS && varExpression.variable().isOutput()){
				throw new CIVLSyntaxException(
						"attempt to read the output variable "
								+ name, source);
			}
			result = varExpression;
		} else if (scope.getFunction(name) != null) {
			result = modelFactory.functionPointerExpression(source,
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
			result = modelFactory.addressOfExpression(source,
					(LHSExpression) arguments.get(0));
			break;
		case BIG_O:
			result = modelFactory.unaryExpression(source, UNARY_OPERATOR.BIG_O,
					arguments.get(0));
			break;
		case DEREFERENCE:
			result = modelFactory.dereferenceExpression(source,
					arguments.get(0));
			break;
		case CONDITIONAL:
			result = modelFactory.conditionalExpression(source,
					arguments.get(0), arguments.get(1), arguments.get(2));
			modelFactory
					.addConditionalExpression((ConditionalExpression) result);
			break;
		case DIV:
			result = modelFactory.binaryExpression(source,
					BINARY_OPERATOR.DIVIDE, arguments.get(0), arguments.get(1));
			break;
		case EQUALS:
			result = modelFactory.binaryExpression(source,
					BINARY_OPERATOR.EQUAL, arguments.get(0), arguments.get(1));
			break;
		case GT:
			result = modelFactory.binaryExpression(source,
					BINARY_OPERATOR.LESS_THAN, arguments.get(1),
					arguments.get(0));
			break;
		case GTE:
			result = modelFactory.binaryExpression(source,
					BINARY_OPERATOR.LESS_THAN_EQUAL, arguments.get(1),
					arguments.get(0));
			break;
		case IMPLIES:
			result = modelFactory
					.binaryExpression(source, BINARY_OPERATOR.IMPLIES,
							arguments.get(0), arguments.get(1));
			break;
		case LAND:
			result = modelFactory.binaryExpression(source, BINARY_OPERATOR.AND,
					arguments.get(0), arguments.get(1));
			break;
		case LOR:
			result = modelFactory.binaryExpression(source, BINARY_OPERATOR.OR,
					arguments.get(0), arguments.get(1));
			break;
		case LT:
			result = modelFactory.binaryExpression(source,
					BINARY_OPERATOR.LESS_THAN, arguments.get(0),
					arguments.get(1));
			break;
		case LTE:
			result = modelFactory.binaryExpression(source,
					BINARY_OPERATOR.LESS_THAN_EQUAL, arguments.get(0),
					arguments.get(1));
			break;
		case MINUS:
			result = modelFactory.binaryExpression(source,
					BINARY_OPERATOR.MINUS, arguments.get(0), arguments.get(1));
			break;
		case MOD:
			result = modelFactory.binaryExpression(source,
					BINARY_OPERATOR.MODULO, arguments.get(0), arguments.get(1));
			break;
		case NEQ:
			result = modelFactory.binaryExpression(source,
					BINARY_OPERATOR.NOT_EQUAL, arguments.get(0),
					arguments.get(1));
			break;
		case NOT:
			result = modelFactory.unaryExpression(source, UNARY_OPERATOR.NOT,
					arguments.get(0));
			break;
		case PLUS:
			result = translatePlusOperation(source, arguments.get(0),
					arguments.get(1));
			break;
		case SUBSCRIPT:
			throw new CIVLInternalException("unreachable", source);
		case TIMES:
			result = modelFactory.binaryExpression(source,
					BINARY_OPERATOR.TIMES, arguments.get(0), arguments.get(1));
			break;
		case UNARYMINUS:
			result = modelFactory.unaryExpression(source,
					UNARY_OPERATOR.NEGATIVE, arguments.get(0));
			break;
		case UNARYPLUS:
			result = arguments.get(0);
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
		Expression lhs = translateExpressionNode(leftNode, scope, true);
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
				modelFactory.setCurrentScope(scope);
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
			return modelFactory.integerType();
		case FLOAT:
		case DOUBLE:
		case LONG_DOUBLE:
		case REAL:
			return modelFactory.realType();
		case BOOL:
			return modelFactory.booleanType();
		case CHAR:
			return modelFactory.charType();
		case DOUBLE_COMPLEX:
		case FLOAT_COMPLEX:
		case LONG_DOUBLE_COMPLEX:
		case SIGNED_CHAR:
		case UNSIGNED_CHAR:
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
		case PROC_TYPE:
			return modelFactory.processType();
		case HEAP_TYPE:
			return modelBuilder.heapType;
		case DYNAMIC_TYPE:
			return modelFactory.dynamicType();
		case BUNDLE_TYPE:
			return modelBuilder.bundleType;
		default:
		}
		result = modelFactory.structOrUnionType(
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
			StructOrUnionField civlField = modelFactory.structField(identifier,
					civlFieldType);

			civlFields[i] = civlField;
		}
		result.complete(civlFields);
		switch (tag) {
		case MESSAGE_TYPE:
			modelBuilder.messageType = result;
			break;
		case QUEUE_TYPE:
			modelBuilder.queueType = result;
			break;
		case COMM_TYPE:
			result.setHandleObjectType(true);
			modelBuilder.commType = result;
			modelBuilder.handledObjectTypes.add(result);
			break;
		case GCOMM_TYPE:
			result.setHandleObjectType(true);
			modelBuilder.gcommType = result;
			modelBuilder.handledObjectTypes.add(result);
			break;
		default:
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
					result = modelFactory
							.completeArrayType(elementType, extent);
				else
					result = modelFactory.incompleteArrayType(elementType);
				break;
			}
			case BASIC:
				result = translateABCBasicType(source,
						(StandardBasicType) abcType);
				break;
			case HEAP:
				result = modelFactory.pointerType(modelBuilder.heapType);
				break;
			case OTHER_INTEGER:
				result = modelFactory.integerType();
				break;
			case POINTER: {
				PointerType pointerType = (PointerType) abcType;
				Type referencedType = pointerType.referencedType();
				CIVLType baseType = translateABCType(source, scope,
						referencedType);

				result = modelFactory.pointerType(baseType);
				break;
			}
			case PROCESS:
				result = modelFactory.processType();
				break;
			case SCOPE:
				result = modelFactory.scopeType();
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
				result = modelFactory.voidType();
				break;
			case ENUMERATION:
				return translateABCEnumerationType(source, scope,
						(EnumerationType) abcType);
			case FUNCTION:
				return translateABCFunctionType(source, scope,
						(FunctionType) abcType);
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
		return modelFactory.functionType(returnType, paraTypes);
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
					modelFactory.dynamicType(), identifier, vid);
			lhs = modelFactory.variableExpression(civlSource, variable);
			scope.addVariable(variable);
			type.setStateVariable(variable);
			if (sourceLocation == null)
				sourceLocation = modelFactory.location(
						modelFactory.sourceOfBeginning(typeNode), scope);
			result = new CommonFragment(sourceLocation,
					modelFactory.assignStatement(civlSource, sourceLocation,
							lhs, rhs, true));
		}
		return result;
	}

	// Getters and Setters
	protected FunctionInfo functionInfo() {
		return this.functionInfo;
	}

	protected CIVLFunction function() {
		return function;
	}

	protected void setFunction(CIVLFunction function) {
		this.function = function;
	}

	protected ModelBuilderWorker modelBuilder() {
		return this.modelBuilder;
	}

	protected ModelFactory modelFactory() {
		return this.modelFactory;
	}
}
