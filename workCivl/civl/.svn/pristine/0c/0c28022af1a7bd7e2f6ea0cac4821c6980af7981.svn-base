package edu.udel.cis.vsl.civl.model.common;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import edu.udel.cis.vsl.abc.ast.entity.IF.Function;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.program.IF.Program;
import edu.udel.cis.vsl.abc.token.IF.CivlcToken;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.TokenFactory;
import edu.udel.cis.vsl.civl.analysis.IF.CodeAnalyzer;
import edu.udel.cis.vsl.civl.model.IF.AbstractFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLException;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLTypeFactory;
import edu.udel.cis.vsl.civl.model.IF.Fragment;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.ModelConfiguration;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.SystemFunction;
import edu.udel.cis.vsl.civl.model.IF.expression.AbstractFunctionCallExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.AddressOfExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ArrayLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression.BINARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.BooleanLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BoundVariableExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.CastExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.CharLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DereferenceExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DerivativeCallExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DomainGuardExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DotExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DynamicTypeOfExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.FunctionGuardExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.FunctionIdentifierExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.HereOrRootExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.InitialValueExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.IntegerLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.MPIContractExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.MPIContractExpression.MPI_CONTRACT_EXPRESSION_KIND;
import edu.udel.cis.vsl.civl.model.IF.expression.MemoryUnitExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Nothing;
import edu.udel.cis.vsl.civl.model.IF.expression.PointerSetExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ProcnullExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.QuantifiedExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.QuantifiedExpression.Quantifier;
import edu.udel.cis.vsl.civl.model.IF.expression.RealLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.RecDomainLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.RegularRangeExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.RemoteExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ScopeofExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SelfExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SizeofExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SizeofTypeExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.StructOrUnionLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SubscriptExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SystemFunctionCallExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SystemGuardExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression.UNARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.WildcardExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.reference.ArraySliceReference;
import edu.udel.cis.vsl.civl.model.IF.expression.reference.ArraySliceReference.ArraySliceKind;
import edu.udel.cis.vsl.civl.model.IF.expression.reference.MemoryUnitReference;
import edu.udel.cis.vsl.civl.model.IF.expression.reference.SelfReference;
import edu.udel.cis.vsl.civl.model.IF.expression.reference.StructOrUnionFieldReference;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.AssignStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.CivlParForSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ContractVerifyStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.DomainIteratorStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.MallocStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.NoopStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPointerType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPrimitiveType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPrimitiveType.PrimitiveTypeKind;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLStructOrUnionType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.model.common.expression.CommonAbstractFunctionCallExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonAddressOfExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonArrayLiteralExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonBinaryExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonBooleanLiteralExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonBoundVariableExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonCastExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonCharLiteralExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonConditionalExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonDereferenceExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonDerivativeCallExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonDomainGuardExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonDotExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonDynamicTypeOfExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonFunctionGuardExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonFunctionIdentifierExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonHereOrRootExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonInitialValueExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonIntegerLiteralExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonMPIContractExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonMemoryUnitExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonNothing;
import edu.udel.cis.vsl.civl.model.common.expression.CommonPointerSetExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonProcnullExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonQuantifiedExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonRealLiteralExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonRecDomainLiteralExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonRegularRangeExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonRemoteExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonScopeofExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonSelfExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonSizeofExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonSizeofTypeExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonStructOrUnionLiteralExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonSubscriptExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonSystemFunctionCallExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonSystemGuardExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonUnaryExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonUndefinedProcessExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonVariableExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonWildcardExpression;
import edu.udel.cis.vsl.civl.model.common.expression.reference.CommonArraySliceReference;
import edu.udel.cis.vsl.civl.model.common.expression.reference.CommonSelfReference;
import edu.udel.cis.vsl.civl.model.common.expression.reference.CommonStructOrUnionFieldReference;
import edu.udel.cis.vsl.civl.model.common.location.CommonLocation;
import edu.udel.cis.vsl.civl.model.common.statement.CommonAssignStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonAtomBranchStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonAtomicLockAssignStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonCallStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonCivlForEnterStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonCivlParForSpawnStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonContractVerifyStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonGotoBranchStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonIfElseBranchStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonLoopBranchStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonMallocStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonNoopStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonReturnStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonSwitchBranchStatement;
import edu.udel.cis.vsl.civl.model.common.variable.CommonVariable;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.civl.util.IF.Singleton;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * The factory to create all model components. Usually this is the only way
 * model components will be created.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class CommonModelFactory implements ModelFactory {

	/* ******************************* Types ******************************* */

	/**
	 * Kinds for temporal variables introduced when translating conditional
	 * expressions that requires temporal variable to store some intermediate
	 * data
	 * 
	 */
	public enum TempVariableKind {
		CONDITIONAL
	}

	/* *************************** Static Fields *************************** */

	/**
	 * The name of the atomic lock variable
	 */
	private static final String CIVL_FILESYSTEM_NAME = "CIVL_filesystem";

	/**
	 * Amount by which to increase the list of cached scope values and process
	 * values when a new value is requested that is outside of the current
	 * range.
	 */
	private final static int CACHE_INCREMENT = 10;

	/**
	 * The prefix of the temporal variables for translating conditional
	 * expressions
	 */
	private static final String CONDITIONAL_VARIABLE_PREFIX = "_cond_var_";

	private static final String DOM_SIZE_PREFIX = "_dom_size";

	private static final String PAR_PROC_PREFIX = "_par_procs";

	/* ************************** Instance Fields ************************** */

	private List<Variable> inputVariables = new LinkedList<>();

	private int domSizeVariableId = 0;

	private int parProcsVariableId = 0;

	private CommonCIVLTypeFactory typeFactory;

	/**
	 * The list of variables created for array literals used to initialize a
	 * pointer type variable. E.g., int* p=(int[]){2,3} will introduce an
	 * anonymous variable int[] __anon0 = {2,3}; int* p = &__anon0[0];
	 */
	private int anonymousVariableId = 0;

	private Fragment anonFragment;

	/**
	 * The unique variable $ATOMIC_LOCK_VAR in the root scope for process that
	 * the executing of $atomic blocks to have the highest priority for
	 * execution.
	 */
	private VariableExpression atomicLockVariableExpression;

	private Variable timeCountVariable;

	private Variable brokenTimeVariable;

	// private Variable symbolicConstantCounter;

	private VariableExpression civlFilesystemVariableExpression;

	/**
	 * The number of conditional expressions that have been encountered, used to
	 * create temporal variable.
	 */
	private int conditionalExpressionCounter = 0;

	/**
	 * The stack of queues of conditional expression.
	 */
	private Stack<ArrayDeque<ConditionalExpression>> conditionalExpressions;

	// private Scope currentScope;

	/** Keep a set of used identifiers for fly-weighting purposes. */
	private Map<String, Identifier> identifiers;

	/** Keep a unique number to identify locations. */
	private int locationID = 0;

	/**
	 * When translating a CallOrSpawnStatement that has some conditional
	 * expressions as its arguments, we need to update the call statement stack
	 * maintained in the model builder worker, because the function field of
	 * each call statement is only updated after the whole AST tree is
	 * traversed.
	 */
	ModelBuilderWorker modelBuilder;

	private List<CodeAnalyzer> codeAnalyzers;

	/** A list of nulls of length CACHE_INCREMENT */
	private List<SymbolicExpression> nullList = new LinkedList<SymbolicExpression>();

	/**
	 * The list of canonicalized symbolic expressions of process IDs, will be
	 * used in Executor, Evaluator and State factory to obtain symbolic process
	 * ID's.
	 */
	private List<SymbolicExpression> processValues = new ArrayList<SymbolicExpression>();

	/** Keep a unique number to identify scopes. */
	private int scopeID = 0;

	/**
	 * The list of canonicalized symbolic expressions of scope IDs, will be used
	 * in Executor, Evaluator and State factory to obtain symbolic scope ID's.
	 */
	private List<SymbolicExpression> scopeValues = new ArrayList<SymbolicExpression>();

	/**
	 * The system source, used to create the identifier of the system function
	 * (_CIVL_System), and for elements introduced during translation but
	 * doesn't have real source, e.g., the atomic lock variable, etc.
	 */
	private CIVLSource systemSource = new SystemCIVLSource();

	/**
	 * The unique ABC token factory, used for obtaining source in the
	 * translation.
	 */
	private TokenFactory tokenFactory;

	/**
	 * The unique symbolic expression for the undefined scope value, which has
	 * the integer value -1.
	 */
	private SymbolicExpression undefinedScopeValue;

	/**
	 * The unique symbolic expression for the null scope value, which has the
	 * integer value -2.
	 */
	private SymbolicExpression nullScopeValue;

	/**
	 * The unique symbolic expression for the undefined process value, which has
	 * the integer value -1.
	 */
	private SymbolicExpression undefinedProcessValue;

	/**
	 * The unique symbolic expression for the null process value, which has the
	 * integer value -2.
	 */
	private SymbolicExpression nullProcessValue;

	/**
	 * The unique SARL symbolic universe used in the system.
	 */
	private SymbolicUniverse universe;

	/**
	 * The unique integer object of zero.
	 */
	private IntObject zeroObj;

	/**
	 * The system scope of the model, i.e., the root scope.
	 */
	private Scope systemScope;

	private FunctionIdentifierExpression waitallFuncPointer = null;

	private FunctionIdentifierExpression elaborateDomainFuncPointer = null;

	/* **************************** Constructors *************************** */

	/**
	 * The factory to create all model components. Usually this is the only way
	 * model components will be created.
	 * 
	 * @param universe
	 *            The symbolic universe
	 */
	public CommonModelFactory(SymbolicUniverse universe) {
		this.typeFactory = new CommonCIVLTypeFactory(universe);
		this.universe = universe;
		this.identifiers = new HashMap<String, Identifier>();

		zeroObj = (IntObject) universe.canonic(universe.intObject(0));
		for (int i = 0; i < CACHE_INCREMENT; i++)
			nullList.add(null);
		undefinedProcessValue = universe.canonic(universe.tuple(
				typeFactory.processSymbolicType,
				new Singleton<SymbolicExpression>(universe.integer(-1))));
		this.nullProcessValue = universe.canonic(universe.tuple(
				typeFactory.processSymbolicType,
				new Singleton<SymbolicExpression>(universe.integer(-2))));
		undefinedScopeValue = universe.canonic(universe.tuple(
				typeFactory.scopeSymbolicType,
				new Singleton<SymbolicExpression>(universe.integer(-1))));
		this.nullScopeValue = universe.canonic(universe.tuple(
				typeFactory.scopeSymbolicType,
				new Singleton<SymbolicExpression>(universe.integer(-2))));
		this.conditionalExpressions = new Stack<ArrayDeque<ConditionalExpression>>();
		this.anonFragment = new CommonFragment();
	}

	/* ********************** Methods from ModelFactory ******************** */

	/* *********************************************************************
	 * CIVL Expressions
	 * *********************************************************************
	 */

	@Override
	public AbstractFunctionCallExpression abstractFunctionCallExpression(
			CIVLSource source, AbstractFunction function,
			List<Expression> arguments) {
		// Note: While the abstract function may be declared in e.g. the
		// outermost scope, since it has no value or state, it doesn't
		// contribute anything non-local to the expression scope.
		Scope expressionScope = joinScope(arguments);
		Scope lowestScope = getLowerScope(arguments);

		return new CommonAbstractFunctionCallExpression(source,
				expressionScope, lowestScope, function, arguments);
	}

	@Override
	public AddressOfExpression addressOfExpression(CIVLSource source,
			LHSExpression operand) {
		return new CommonAddressOfExpression(source,
				typeFactory.pointerType(operand.getExpressionType()), operand);
	}

	/**
	 * A binary expression. One of {+,-,*,\,<,<=,==,!=,&&,||,%}
	 * 
	 * @param operator
	 *            The binary operator.
	 * @param left
	 *            The left operand.
	 * @param right
	 *            The right operand.
	 * @return The binary expression.
	 */
	@Override
	public BinaryExpression binaryExpression(CIVLSource source,
			BINARY_OPERATOR operator, Expression left, Expression right) {
		Scope expressionScope = join(left.expressionScope(),
				right.expressionScope());
		Scope lowestScope = getLower(left.lowestScope(), right.lowestScope());

		switch (operator) {
		case AND:
		case EQUAL:
		case LESS_THAN:
		case LESS_THAN_EQUAL:
		case NOT_EQUAL:
		case OR:
			return new CommonBinaryExpression(source, expressionScope,
					lowestScope, typeFactory.booleanType, operator, left, right);
		case PLUS:
		case TIMES:
		case DIVIDE:
		case MINUS:
		case MODULO:
		default:
			CIVLType leftType = left.getExpressionType();
			CIVLType rightType = right.getExpressionType();
			CIVLType resultType;

			// Types should be the same unless we're doing pointer arithmetic.
			if (leftType.equals(rightType)) {
				// ((CommonBinaryExpression)
				// result).setExpressionType(leftType);
				resultType = leftType;
			} else if (leftType instanceof CIVLPointerType
					&& rightType instanceof CIVLPrimitiveType) {
				assert ((CIVLPrimitiveType) rightType).primitiveTypeKind() == PrimitiveTypeKind.INT;
				// ((CommonBinaryExpression)
				// result).setExpressionType(leftType);
				resultType = leftType;
			} else if (leftType instanceof CIVLPointerType
					&& rightType instanceof CIVLPrimitiveType) {
				assert ((CIVLPrimitiveType) rightType).primitiveTypeKind() == PrimitiveTypeKind.INT;
				// ((CommonBinaryExpression)
				// result).setExpressionType(leftType);
				resultType = leftType;
			} else if (leftType instanceof CIVLPointerType
					&& rightType instanceof CIVLPointerType) {
				// compatibility checking
				if (((CIVLPointerType) leftType).baseType().equals(
						((CIVLPointerType) rightType).baseType()))
					// ((CommonBinaryExpression) result)
					// .setExpressionType(integerType());
					resultType = typeFactory.integerType;
				else
					throw new CIVLException(leftType + " and " + rightType
							+ " are not pointers to compatiable types", source);
			} else
				throw new CIVLException("Incompatible types to +", source);
			return new CommonBinaryExpression(source, expressionScope,
					lowestScope, resultType, operator, left, right);
		}
	}

	@Override
	public Expression booleanExpression(Expression expression)
			throws ModelFactoryException {
		CIVLSource source = expression.getSource();

		if (!expression.getExpressionType().equals(typeFactory.booleanType)) {
			CIVLType exprType = expression.getExpressionType();

			if (exprType.equals(typeFactory.integerType)) {
				expression = binaryExpression(source,
						BINARY_OPERATOR.NOT_EQUAL, expression,
						integerLiteralExpression(source, BigInteger.ZERO));
			} else if (exprType.equals(typeFactory.realType)) {
				expression = binaryExpression(source,
						BINARY_OPERATOR.NOT_EQUAL, expression,
						realLiteralExpression(source, BigDecimal.ZERO));
			} else if (exprType.isPointerType()) {
				CIVLPointerType pointerType = (CIVLPointerType) expression
						.getExpressionType();

				expression = binaryExpression(source,
						BINARY_OPERATOR.NOT_EQUAL, expression,
						this.nullPointerExpression(pointerType, source));
			} else if (exprType.isCharType()) {
				expression = binaryExpression(source,
						BINARY_OPERATOR.NOT_EQUAL, expression,
						this.charLiteralExpression(source, (char) 0));
			} else {
				throw new ModelFactoryException("The expression " + expression
						+ " isn't compatible with boolean type",
						expression.getSource());
			}
		}
		return expression;
	}

	@Override
	public Expression numericExpression(Expression expression)
			throws ModelFactoryException {
		CIVLType type = expression.getExpressionType();

		if (type.isNumericType() || type.isPointerType() || type.isScopeType()
				|| type.isArrayType())
			return expression;
		if (type.isBoolType())
			return this.castExpression(expression.getSource(),
					typeFactory.integerType(), expression);
		if (type.isCharType())
			return this.castExpression(expression.getSource(),
					typeFactory.integerType(), expression);
		throw new ModelFactoryException("The expression " + expression
				+ " isn't compatible with numeric type", expression.getSource());
	}

	/**
	 * A boolean literal expression.
	 * 
	 * @param value
	 *            True or false.
	 * @return The boolean literal expression.
	 */
	@Override
	public BooleanLiteralExpression booleanLiteralExpression(CIVLSource source,
			boolean value) {
		return new CommonBooleanLiteralExpression(source,
				typeFactory.booleanType, value);
	}

	@Override
	public BoundVariableExpression boundVariableExpression(CIVLSource source,
			Identifier name, CIVLType type) {
		return new CommonBoundVariableExpression(source, type, name);
	}

	/**
	 * The ternary conditional expression ("?" in C).
	 * 
	 * @param condition
	 *            The condition being evaluated in this conditional.
	 * @param trueBranch
	 *            The expression returned if the condition evaluates to true.
	 * @param falseBranch
	 *            The expression returned if the condition evaluates to false.
	 * @return The conditional expression.
	 */
	@Override
	public ConditionalExpression conditionalExpression(CIVLSource source,
			Expression condition, Expression trueBranch, Expression falseBranch) {
		assert trueBranch.getExpressionType().equals(
				falseBranch.getExpressionType());

		return new CommonConditionalExpression(
				source,
				joinScope(Arrays.asList(condition, trueBranch, falseBranch)),
				getLowerScope(Arrays.asList(condition, trueBranch, falseBranch)),
				trueBranch.getExpressionType(), condition, trueBranch,
				falseBranch);
	}

	@Override
	public CastExpression castExpression(CIVLSource source, CIVLType type,
			Expression expression) {
		return new CommonCastExpression(source, expression.expressionScope(),
				type, expression);
	}

	@Override
	public DereferenceExpression dereferenceExpression(CIVLSource source,
			Expression pointer) {
		CIVLPointerType pointerType = (CIVLPointerType) pointer
				.getExpressionType();

		// systemScope: indicates unknown scope
		return new CommonDereferenceExpression(source, this.systemScope,
				pointerType.baseType(), pointer);
	}

	@Override
	public DerivativeCallExpression derivativeCallExpression(CIVLSource source,
			AbstractFunction function,
			List<Pair<Variable, IntegerLiteralExpression>> partials,
			List<Expression> arguments) {
		return new CommonDerivativeCallExpression(source, joinScope(arguments),
				getLowerScope(arguments), function, partials, arguments);
	}

	@Override
	public DotExpression dotExpression(CIVLSource source, Expression struct,
			int fieldIndex) {
		assert struct.getExpressionType() instanceof CIVLStructOrUnionType;
		return new CommonDotExpression(source, struct, fieldIndex);
	}

	@Override
	public DynamicTypeOfExpression dynamicTypeOfExpression(CIVLSource source,
			CIVLType type) {
		return new CommonDynamicTypeOfExpression(source,
				typeFactory.dynamicType, type);
	}

	@Override
	public FunctionIdentifierExpression functionIdentifierExpression(
			CIVLSource source, CIVLFunction function) {
		FunctionIdentifierExpression expression = new CommonFunctionIdentifierExpression(
				source, function, typeFactory.pointerSymbolicType);

		return expression;
	}

	@Override
	public HereOrRootExpression hereOrRootExpression(CIVLSource source,
			boolean isRoot) {
		return new CommonHereOrRootExpression(source, typeFactory.scopeType,
				isRoot, isRoot ? this.scopeValue(this.systemScope.id()) : null);
	}

	@Override
	public InitialValueExpression initialValueExpression(CIVLSource source,
			Variable variable) {
		return new CommonInitialValueExpression(source, variable);
	}

	/**
	 * An integer literal expression.
	 * 
	 * @param value
	 *            The (arbitrary precision) integer value.
	 * @return The integer literal expression.
	 */
	@Override
	public IntegerLiteralExpression integerLiteralExpression(CIVLSource source,
			BigInteger value) {
		return new CommonIntegerLiteralExpression(source,
				typeFactory.integerType, value);
	}

	@Override
	public Expression nullPointerExpression(CIVLPointerType pointerType,
			CIVLSource source) {
		Expression zero = integerLiteralExpression(source, BigInteger.ZERO);
		Expression result;

		result = castExpression(source, pointerType, zero);
		return result;
	}

	@Override
	public QuantifiedExpression quantifiedExpression(CIVLSource source,
			Quantifier quantifier, Identifier boundVariableName,
			CIVLType boundVariableType, Expression restriction,
			Expression expression) {
		return new CommonQuantifiedExpression(source, join(
				expression.expressionScope(), restriction.expressionScope()),
				typeFactory.booleanType, quantifier, boundVariableName,
				boundVariableType, restriction, expression);
	}

	@Override
	public QuantifiedExpression quantifiedExpression(CIVLSource source,
			Quantifier quantifier, Identifier boundVariableName,
			CIVLType boundVariableType, Expression lower, Expression upper,
			Expression expression) {
		return new CommonQuantifiedExpression(source, join(
				join(expression.expressionScope(), lower.expressionScope()),
				upper.expressionScope()), typeFactory.booleanType, quantifier,
				boundVariableName, boundVariableType, lower, upper, expression);
	}

	/**
	 * A real literal expression.
	 * 
	 * @param value
	 *            The (arbitrary precision) real value.
	 * @return The real literal expression.
	 */
	@Override
	public RealLiteralExpression realLiteralExpression(CIVLSource source,
			BigDecimal value) {
		return new CommonRealLiteralExpression(source, typeFactory.realType,
				value);
	}

	@Override
	public ScopeofExpression scopeofExpression(CIVLSource source,
			LHSExpression argument) {
		return new CommonScopeofExpression(source, typeFactory.scopeType,
				argument);
	}

	/**
	 * A self expression. Used to referenced the current process.
	 * 
	 * @return A new self expression.
	 */
	@Override
	public SelfExpression selfExpression(CIVLSource source) {
		return new CommonSelfExpression(source, typeFactory.processType);
	}

	@Override
	public ProcnullExpression procnullExpression(CIVLSource source) {
		return new CommonProcnullExpression(source, typeFactory.processType,
				this.nullProcessValue);
	}

	@Override
	public SizeofExpression sizeofExpressionExpression(CIVLSource source,
			Expression argument) {
		return new CommonSizeofExpression(source, typeFactory.integerType,
				argument);
	}

	@Override
	public RemoteExpression remoteExpression(CIVLSource source,
			VariableExpression expression, Expression process, Scope scope) {
		// TODO: what's lowest scope ?
		return new CommonRemoteExpression(source, scope, process.lowestScope(),
				expression.getExpressionType(), expression, process);
	}

	@Override
	public SizeofTypeExpression sizeofTypeExpression(CIVLSource source,
			CIVLType type) {
		Variable typeStateVariable = type.getStateVariable();
		Scope expressionScope = null;

		// If the type has a state variable, then the scope of the sizeof
		// expression is the scope of the state variable; otherwise, the scope
		// of the sizeof expression is NULL
		if (typeStateVariable != null) {
			expressionScope = typeStateVariable.scope();
		}
		return new CommonSizeofTypeExpression(source, expressionScope,
				typeFactory.integerType, type);
	}

	/**
	 * An expression for an array index operation. e.g. a[i]
	 * 
	 * @param array
	 *            An expression evaluating to an array.
	 * @param index
	 *            An expression evaluating to an integer.
	 * @return The array index expression.
	 */
	@Override
	public SubscriptExpression subscriptExpression(CIVLSource source,
			LHSExpression array, Expression index) {
		CIVLType arrayType = array.getExpressionType();
		CIVLType expressionType;

		if (arrayType instanceof CIVLArrayType)
			expressionType = ((CIVLArrayType) arrayType).elementType();
		else if (arrayType instanceof CIVLPointerType)
			expressionType = ((CIVLPointerType) arrayType).baseType();
		else
			throw new CIVLInternalException(
					"Unable to set expression type for the subscript expression: ",
					source);
		return new CommonSubscriptExpression(source, join(
				array.expressionScope(), index.expressionScope()), getLower(
				array.lowestScope(), index.lowestScope()), expressionType,
				array, index);
	}

	@Override
	public SystemFunctionCallExpression systemFunctionCallExpression(
			CallOrSpawnStatement callStatement) {
		return new CommonSystemFunctionCallExpression(
				callStatement.getSource(), callStatement);
	}

	/**
	 * A unary expression. One of {-,!}.
	 * 
	 * @param operator
	 *            The unary operator.
	 * @param operand
	 *            The expression to which the operator is applied.
	 * @return The unary expression.
	 */
	@Override
	public UnaryExpression unaryExpression(CIVLSource source,
			UNARY_OPERATOR operator, Expression operand) {
		switch (operator) {
		case NEGATIVE:
		case BIG_O:
			return new CommonUnaryExpression(source,
					operand.getExpressionType(), operator, operand);
		case NOT:
			assert operand.getExpressionType().isBoolType();
			return new CommonUnaryExpression(source, typeFactory.booleanType,
					operator, operand);
		case VALID:
			assert operand instanceof PointerSetExpression;
			return new CommonUnaryExpression(source, typeFactory.booleanType,
					operator, operand);
		default:
			throw new CIVLInternalException("Unknown unary operator: "
					+ operator, source);

		}
	}

	/**
	 * A variable expression.
	 * 
	 * @param variable
	 *            The variable being referenced.
	 * @return The variable expression.
	 */
	@Override
	public VariableExpression variableExpression(CIVLSource source,
			Variable variable) {
		return new CommonVariableExpression(source, variable);
	}

	/* *********************************************************************
	 * Fragments and Statements
	 * *********************************************************************
	 */

	@Override
	public AssignStatement assignStatement(CIVLSource civlSource,
			Location source, LHSExpression lhs, Expression rhs,
			boolean isInitialization) {
		return new CommonAssignStatement(civlSource, join(
				lhs.expressionScope(), rhs.expressionScope()), getLower(
				lhs.lowestScope(), rhs.lowestScope()), source,
				this.trueExpression(civlSource), lhs, rhs, isInitialization);
	}

	@Override
	public Expression trueExpression(CIVLSource civlSource) {
		return this.booleanLiteralExpression(civlSource, true);
	}

	// @Override
	// public Fragment assumeFragment(CIVLSource civlSource, Location source,
	// Expression expression) {
	// return new CommonFragment(new CommonAssumeStatement(civlSource, source,
	// this.trueExpression(civlSource), expression));
	// }
	//
	// @Override
	// public Fragment assertFragment(CIVLSource civlSource, Location source,
	// Expression condition, Expression[] explanation) {
	// Scope statementScope = condition.expressionScope();
	// Scope lowestScope = condition.lowestScope();
	// Scope lowestScopeExplanation = getLower(explanation);
	//
	// if (explanation != null)
	// for (Expression arg : explanation) {
	// statementScope = join(statementScope, arg.expressionScope());
	// }
	// return new CommonFragment(
	// new CommonAssertStatement(civlSource, statementScope, getLower(
	// lowestScope, lowestScopeExplanation), source, this
	// .trueExpression(civlSource), condition, explanation));
	// }

	@Override
	public Fragment atomicFragment(boolean deterministic, Fragment fragment,
			Location start, Location end) {
		Statement enterAtomic;
		Statement leaveAtomic;
		Fragment startFragment;
		Fragment endFragment;
		Fragment result;
		Expression startGuard = null;

		if (deterministic) {
			enterAtomic = new CommonAtomBranchStatement(start.getSource(),
					start, this.trueExpression(start.getSource()), true);
			leaveAtomic = new CommonAtomBranchStatement(end.getSource(), end,
					this.trueExpression(end.getSource()), false);
		} else {
			enterAtomic = new CommonAtomicLockAssignStatement(
					start.getSource(), this.systemScope, this.systemScope,
					start, this.trueExpression(start.getSource()), true,
					this.atomicLockVariableExpression,
					this.selfExpression(systemSource));
			leaveAtomic = new CommonAtomicLockAssignStatement(
					end.getSource(),
					this.systemScope,
					this.systemScope,
					end,
					this.trueExpression(end.getSource()),
					false,
					this.atomicLockVariableExpression,
					new CommonUndefinedProcessExpression(systemSource,
							typeFactory.processType, this.undefinedProcessValue));
		}
		startFragment = new CommonFragment(enterAtomic);
		endFragment = new CommonFragment(leaveAtomic);
		start.setEnterAtomic(deterministic);

		if (fragment.startLocation().getNumOutgoing() == 1) {
			Statement firstStmtOfBody = fragment.startLocation()
					.getSoleOutgoing();

			startGuard = firstStmtOfBody.guard();
			firstStmtOfBody
					.setGuard(this.trueExpression(startGuard.getSource()));
		} else {
			for (Statement statement : fragment.startLocation().outgoing()) {
				if (startGuard == null)
					startGuard = statement.guard();
				else {
					startGuard = this.binaryExpression(startGuard.getSource(),
							BINARY_OPERATOR.OR, startGuard, statement.guard());
				}
			}
		}
		if (startGuard != null)
			enterAtomic.setGuard(startGuard);
		end.setLeaveAtomic(deterministic);
		result = startFragment.combineWith(fragment);
		result = result.combineWith(endFragment);
		return result;
	}

	@Override
	public CallOrSpawnStatement callOrSpawnStatement(CIVLSource civlSource,
			Location source, boolean isCall, Expression function,
			List<Expression> arguments, Expression guard) {
		Scope statementScope = null;

		for (Expression arg : arguments) {
			statementScope = join(statementScope, arg.expressionScope());
		}
		return new CommonCallStatement(civlSource, statementScope,
				getLowerScope(arguments), source, guard != null ? guard
						: this.trueExpression(civlSource), isCall, null,
				function, arguments);
	}

	@Override
	public NoopStatement gotoBranchStatement(CIVLSource civlSource,
			Location source, String label) {
		return new CommonGotoBranchStatement(civlSource, source,
				this.trueExpression(civlSource), label);
	}

	@Override
	public NoopStatement ifElseBranchStatement(CIVLSource civlSource,
			Location source, Expression guard, boolean isTrue) {
		return new CommonIfElseBranchStatement(civlSource, source,
				guard != null ? guard : this.trueExpression(civlSource), isTrue);
	}

	@Override
	public NoopStatement loopBranchStatement(CIVLSource civlSource,
			Location source, Expression guard, boolean isTrue) {
		return new CommonLoopBranchStatement(civlSource, source,
				guard != null ? guard : this.trueExpression(civlSource), isTrue);
	}

	@Override
	public MallocStatement mallocStatement(CIVLSource civlSource,
			Location source, LHSExpression lhs, CIVLType staticElementType,
			Expression scopeExpression, Expression sizeExpression,
			int mallocId, Expression guard) {
		SymbolicType dynamicElementType = staticElementType
				.getDynamicType(universe);
		SymbolicArrayType dynamicObjectType = (SymbolicArrayType) universe
				.canonic(universe.arrayType(dynamicElementType));
		SymbolicExpression undefinedObject = undefinedValue(dynamicObjectType);

		return new CommonMallocStatement(civlSource, null,
				getLowerScope(Arrays.asList(lhs, scopeExpression,
						sizeExpression)), source, guard != null ? guard
						: this.trueExpression(civlSource), mallocId,
				scopeExpression, staticElementType, dynamicElementType,
				dynamicObjectType, sizeExpression, undefinedObject, lhs);
	}

	@Override
	public NoopStatement noopStatement(CIVLSource civlSource, Location source,
			Expression expression) {
		return new CommonNoopStatement(civlSource, source,
				this.trueExpression(civlSource), expression);
	}

	/**
	 * A noop statement.
	 * 
	 * @param source
	 *            The source location for this noop statement.
	 * @return A new noop statement.
	 */
	@Override
	public NoopStatement noopStatementWtGuard(CIVLSource civlSource,
			Location source, Expression guard) {
		return new CommonNoopStatement(civlSource, source,
				guard != null ? guard : this.trueExpression(civlSource), null);
	}

	@Override
	public NoopStatement switchBranchStatement(CIVLSource civlSource,
			Location source, Expression guard, Expression label) {
		return new CommonSwitchBranchStatement(civlSource, source,
				guard != null ? guard : this.trueExpression(civlSource), label);
	}

	@Override
	public NoopStatement switchBranchStatement(CIVLSource civlSource,
			Location source, Expression guard) {
		return new CommonSwitchBranchStatement(civlSource, source,
				guard != null ? guard : this.trueExpression(civlSource));
	}

	@Override
	public Fragment returnFragment(CIVLSource civlSource, Location source,
			Expression expression, CIVLFunction function) {
		return new CommonFragment(new CommonReturnStatement(civlSource, source,
				this.trueExpression(civlSource), expression, function));
	}

	/* *********************************************************************
	 * CIVL Source
	 * *********************************************************************
	 */

	@Override
	public CIVLSource sourceOf(ASTNode node) {
		return sourceOf(node.getSource());
	}

	@Override
	public CIVLSource sourceOf(Source abcSource) {
		return new ABC_CIVLSource(abcSource);
	}

	@Override
	public CIVLSource sourceOfBeginning(ASTNode node) {
		return sourceOfToken(node.getSource().getFirstToken());
	}

	@Override
	public CIVLSource sourceOfEnd(ASTNode node) {
		return sourceOfToken(node.getSource().getLastToken());
	}

	@Override
	public CIVLSource sourceOfSpan(ASTNode node1, ASTNode node2) {
		return sourceOfSpan(node1.getSource(), node2.getSource());
	}

	@Override
	public CIVLSource sourceOfSpan(CIVLSource source1, CIVLSource source2) {
		return sourceOfSpan(((ABC_CIVLSource) source1).getABCSource(),
				((ABC_CIVLSource) source2).getABCSource());
	}

	@Override
	public CIVLSource sourceOfSpan(Source abcSource1, Source abcSource2) {
		return sourceOf(tokenFactory.join(abcSource1, abcSource2));
	}

	@Override
	public CIVLSource sourceOfToken(CivlcToken token) {
		return sourceOf(tokenFactory.newSource(token));
	}

	/* *********************************************************************
	 * Translating away conditional expressions
	 * *********************************************************************
	 */

	@Override
	public void addConditionalExpression(ConditionalExpression expression) {
		this.conditionalExpressions.peek().add(expression);
	}

	@Override
	public void addConditionalExpressionQueue() {
		conditionalExpressions.add(new ArrayDeque<ConditionalExpression>());
	}

	@Override
	public Fragment conditionalExpressionToIf(ConditionalExpression expression,
			Statement statement) {
		Expression guard = statement.guard();
		Location startLocation = statement.source();
		Expression ifGuard = expression.getCondition(), elseGuard;
		Statement ifBranch, elseBranch;
		Expression ifValue = expression.getTrueBranch(), elseValue = expression
				.getFalseBranch();
		Fragment result = new CommonFragment();
		Set<Statement> lastStatements = new HashSet<>();

		assert ifGuard.getExpressionType().isBoolType();
		elseGuard = unaryExpression(ifGuard.getSource(), UNARY_OPERATOR.NOT,
				ifGuard);
		if (!isTrue(guard)) {
			ifGuard = binaryExpression(
					sourceOfSpan(guard.getSource(), ifGuard.getSource()),
					BINARY_OPERATOR.AND, guard, ifGuard);
			elseGuard = binaryExpression(
					sourceOfSpan(guard.getSource(), elseGuard.getSource()),
					BINARY_OPERATOR.AND, guard, elseGuard);
		}

		if (statement instanceof CallOrSpawnStatement) {
			Function function = modelBuilder.callStatements.get(statement);
			Fragment ifFragment, elseFragment;
			Location ifLocation, elseLocation;
			Scope scope = startLocation.scope();

			ifFragment = new CommonFragment(ifElseBranchStatement(
					ifGuard.getSource(), startLocation, ifGuard, true));
			ifLocation = location(ifValue.getSource(), scope);
			ifBranch = statement.replaceWith(expression, ifValue);
			ifBranch.setGuard(guard);
			ifBranch.setSource(ifLocation);
			ifFragment = ifFragment.combineWith(new CommonFragment(ifBranch));
			elseFragment = new CommonFragment(ifElseBranchStatement(
					elseGuard.getSource(), startLocation, elseGuard, false));
			elseLocation = location(elseValue.getSource(), scope);
			elseBranch = statement.replaceWith(expression, elseValue);
			elseBranch.setGuard(guard);
			elseBranch.setSource(elseLocation);
			elseFragment = elseFragment.combineWith(new CommonFragment(
					elseBranch));
			// remove the old call or spawn statement from the callStatements
			// map and add the two new ones into the map.
			modelBuilder.callStatements.put((CallOrSpawnStatement) ifBranch,
					function);
			modelBuilder.callStatements.put((CallOrSpawnStatement) elseBranch,
					function);
			modelBuilder.callStatements.remove(statement);
			result = ifFragment.parallelCombineWith(elseFragment);

		} else {
			ifBranch = statement.replaceWith(expression, ifValue);
			ifBranch.setCIVLSource(this.expandedSource(ifValue.getSource(),
					statement.getSource()));
			elseBranch = statement.replaceWith(expression, elseValue);
			elseBranch.setCIVLSource(this.expandedSource(elseValue.getSource(),
					statement.getSource()));
			ifBranch.setGuard(ifGuard);
			elseBranch.setGuard(elseGuard);
			lastStatements.add(ifBranch);
			lastStatements.add(elseBranch);
			result.setStartLocation(startLocation);
			result.setFinalStatements(lastStatements);
		}
		startLocation.removeOutgoing(statement);
		return result;
	}

	private CIVLSource expandedSource(CIVLSource expanded, CIVLSource base) {
		return new ExpandedCIVL(expanded, base);
	}

	@Override
	public Fragment conditionalExpressionToIf(Expression guard,
			VariableExpression variable, ConditionalExpression expression) {
		Expression ifGuard = expression.getCondition(), elseGuard;
		Location startLocation = location(ifGuard.getSource(), variable
				.variable().scope());
		Statement ifAssign, elseAssign;
		Expression ifValue = expression.getTrueBranch(), elseValue = expression
				.getFalseBranch();
		Fragment result = new CommonFragment();
		Set<Statement> lastStatements = new HashSet<>();

		assert ifGuard.getExpressionType().isBoolType();
		elseGuard = unaryExpression(ifGuard.getSource(), UNARY_OPERATOR.NOT,
				ifGuard);
		if (guard != null) {
			if (!isTrue(guard)) {
				ifGuard = binaryExpression(
						sourceOfSpan(guard.getSource(), ifGuard.getSource()),
						BINARY_OPERATOR.AND, guard, ifGuard);
				elseGuard = binaryExpression(
						sourceOfSpan(guard.getSource(), elseGuard.getSource()),
						BINARY_OPERATOR.AND, guard, elseGuard);
			}
		}
		ifAssign = assignStatement(ifValue.getSource(), startLocation,
				variable, ifValue, false);
		ifAssign.setGuard(ifGuard);
		lastStatements.add(ifAssign);
		elseAssign = assignStatement(elseValue.getSource(), startLocation,
				variable, elseValue, false);
		elseAssign.setGuard(elseGuard);
		lastStatements.add(elseAssign);
		result.setStartLocation(startLocation);
		result.setFinalStatements(lastStatements);
		return result;
	}

	@Override
	public boolean hasConditionalExpressions() {
		if (!conditionalExpressions.peek().isEmpty())
			return true;
		return false;
	}

	@Override
	public Pair<Fragment, Expression> refineConditionalExpression(Scope scope,
			Expression expression, CIVLSource startSource, CIVLSource endSource) {
		Fragment beforeConditionFragment = new CommonFragment();

		while (hasConditionalExpressions()) {
			ConditionalExpression conditionalExpression = pollFirstConditionaExpression();
			VariableExpression variable = tempVariable(
					TempVariableKind.CONDITIONAL, scope,
					conditionalExpression.getSource(),
					conditionalExpression.getExpressionType());

			beforeConditionFragment = conditionalExpressionToIf(null, variable,
					conditionalExpression);
			if (expression == conditionalExpression)
				expression = variable;
			else
				expression.replaceWith(conditionalExpression, variable);
		}
		if (!beforeConditionFragment.isEmpty()) {
			// make the if-else statements atomic ($atomic)
			beforeConditionFragment = this.insertNoopAtBeginning(startSource,
					scope, beforeConditionFragment);
			beforeConditionFragment = this.atomicFragment(false,
					beforeConditionFragment, this.location(startSource, scope),
					this.location(endSource, scope));
		}
		return new Pair<Fragment, Expression>(beforeConditionFragment,
				expression);
	}

	private Fragment insertNoopAtBeginning(CIVLSource source, Scope scope,
			Fragment old) {
		Location start = location(source, scope);
		NoopStatement noop = noopStatementTemporary(source, start);
		Fragment noopFragment = new CommonFragment(noop);

		return noopFragment.combineWith(old);
	}

	@Override
	public Fragment refineConditionalExpressionOfStatement(Statement statement,
			Location oldLocation) {
		Fragment result = new CommonFragment();
		CIVLSource statementSource = statement.getSource();
		Scope scope = statement.source().scope();

		if (sizeofTopConditionalExpressionQueue() == 1)
			return this.conditionalExpressionToIf(
					this.pollFirstConditionaExpression(), statement);
		while (hasConditionalExpressions()) {
			ConditionalExpression conditionalExpression = pollFirstConditionaExpression();
			VariableExpression variable = tempVariable(
					TempVariableKind.CONDITIONAL, scope,
					conditionalExpression.getSource(),
					conditionalExpression.getExpressionType());
			Fragment ifElse = conditionalExpressionToIf(statement.guard(),
					variable, conditionalExpression);

			statement.replaceWith(conditionalExpression, variable);
			result = result.combineWith(ifElse);
		}
		result = this.insertNoopAtBeginning(statementSource, scope, result);
		// make the if-else statements atomic
		result = this.atomicFragment(false, result,
				this.location(statementSource, scope),
				this.location(statementSource, scope));
		result = result.combineWith(new CommonFragment(statement));
		return result;
	}

	@Override
	public void popConditionaExpressionStack() {
		conditionalExpressions.pop();
	}

	/* *********************************************************************
	 * Atomic Lock Variable
	 * *********************************************************************
	 */

	@Override
	public VariableExpression atomicLockVariableExpression() {
		return this.atomicLockVariableExpression;
	}

	@Override
	public Variable timeCountVariable() {
		return this.timeCountVariable;
	}

	@Override
	public Variable brokenTimeVariable() {
		return this.brokenTimeVariable;
	}

	/* *********************************************************************
	 * Other helper methods
	 * *********************************************************************
	 */

	@Override
	public void computeImpactScopeOfLocation(Location location) {
		if (location.enterAtom() || location.enterAtomic()) {
			Stack<Integer> atomFlags = new Stack<Integer>();
			Set<Integer> checkedLocations = new HashSet<Integer>();
			Scope impactScope = null;
			Stack<Location> workings = new Stack<Location>();

			workings.add(location);
			// DFS searching for reachable statements inside the $atomic/$atom
			// block
			while (!workings.isEmpty()) {
				Location currentLocation = workings.pop();

				checkedLocations.add(currentLocation.id());
				if (location.enterAtom() && currentLocation.enterAtom())
					atomFlags.push(1);
				if (location.enterAtomic() && currentLocation.enterAtomic())
					atomFlags.push(1);
				if (location.enterAtom() && currentLocation.leaveAtom())
					atomFlags.pop();
				if (location.enterAtomic() && currentLocation.leaveAtomic())
					atomFlags.pop();
				if (atomFlags.isEmpty()) {
					if (location.enterAtom()) {
						if (!currentLocation.enterAtom())
							atomFlags.push(1);
					}
					if (location.enterAtomic()) {
						if (!currentLocation.enterAtomic())
							atomFlags.push(1);
					}
					continue;
				}
				if (currentLocation.getNumOutgoing() > 0) {
					int number = currentLocation.getNumOutgoing();
					for (int i = 0; i < number; i++) {
						Statement s = currentLocation.getOutgoing(i);

						if (s instanceof CallOrSpawnStatement) {
							if (((CallOrSpawnStatement) s).isCall()) {
								// calling a function is considered as impact
								// scope because we don't keep record of the
								// total impact scope of a function
								location.setImpactScopeOfAtomicOrAtomBlock(systemScope);
								return;
							}
						}
						if (impactScope == null)
							impactScope = s.statementScope();
						else
							impactScope = join(impactScope, s.statementScope());
						if (impactScope != null
								&& impactScope.id() == systemScope.id()) {
							location.setImpactScopeOfAtomicOrAtomBlock(impactScope);
							return;
						}
						if (s.target() != null) {
							if (!checkedLocations.contains(s.target().id())) {
								workings.push(s.target());

							}
						}
					}
				}
			}
			location.setImpactScopeOfAtomicOrAtomBlock(impactScope);
			return;
		}
	}

	@Override
	public SymbolicExpression nullProcessValue() {
		return this.nullProcessValue;
	}

	@Override
	public boolean isTrue(Expression expression) {
		return expression instanceof BooleanLiteralExpression
				&& ((BooleanLiteralExpression) expression).value();
	}

	@Override
	public SymbolicUniverse universe() {
		return universe;
	}

	@Override
	public AbstractFunction abstractFunction(CIVLSource source,
			Identifier name, List<Variable> parameters, CIVLType returnType,
			Scope containingScope, int continuity) {
		return new CommonAbstractFunction(source, name, parameters, returnType,
				containingScope, containingScope.numFunctions(), continuity,
				this);
	}

	@Override
	public CIVLFunction function(CIVLSource source, boolean isAtomic,
			Identifier name, List<Variable> parameters, CIVLType returnType,
			Scope containingScope, Location startLocation) {
		for (Variable v : parameters) {
			if (v.type().isArrayType()) {
				throw new CIVLInternalException("Parameter of array type.", v);
			}
		}
		return new CommonFunction(source, isAtomic, name, parameters,
				returnType, containingScope,
				containingScope != null ? containingScope.numFunctions() : -1,
				startLocation, this);
	}

	@Override
	public Identifier identifier(CIVLSource source, String name) {
		Identifier result = identifiers.get(name);

		if (result == null) {
			StringObject stringObject = (StringObject) universe
					.canonic(universe.stringObject(name));

			result = new CommonIdentifier(source, stringObject);
			identifiers.put(name, result);
		}
		return result;
	}

	@Override
	public Location location(CIVLSource source, Scope scope) {
		return new CommonLocation(source, scope, locationID++);
	}

	@Override
	public Model model(CIVLSource civlSource, CIVLFunction system,
			Program program) {
		return new CommonModel(civlSource, this, system, program);
	}

	@Override
	public Scope scope(CIVLSource source, Scope parent,
			Set<Variable> variables, CIVLFunction function) {
		Scope newScope;
		Variable heapVariable;
		Set<Variable> myVariables = new HashSet<Variable>();

		heapVariable = this.variable(source, modelBuilder.heapType,
				this.identifier(source, ModelConfiguration.HEAP_VAR), 0);
		myVariables.add(heapVariable);
		myVariables.addAll(variables);
		newScope = new CommonScope(source, parent, myVariables, scopeID++);
		if (newScope.id() == 0) {
			this.createAtomicLockVariable(newScope);
			// if (modelBuilder.timeLibIncluded)
			createTimeVariables(newScope);
			createSymbolicInputCounter(newScope);
			createSymbolicConstantCounter(newScope);
		}
		if (parent != null) {
			parent.addChild(newScope);
		}
		newScope.setFunction(function);
		return newScope;
	}

	@Override
	public void setTokenFactory(TokenFactory tokens) {
		this.tokenFactory = tokens;
	}

	@Override
	public SystemFunction systemFunction(CIVLSource source, Identifier name,
			List<Variable> parameters, CIVLType returnType,
			Scope containingScope, String libraryName) {
		if (libraryName.startsWith("civl-")) {
			libraryName = libraryName.substring(5, libraryName.length());
		} else if (libraryName.endsWith("-common")) {
			libraryName = libraryName.substring(0, libraryName.length() - 7);
		} else if (libraryName.startsWith("civlc-")) {
			libraryName = "civlc";
		} else {
			switch (name.name()) {
			case "printf":
				libraryName = "stdio";
				break;
			case "strcpy":
				libraryName = "string";
				break;
			case "exit":
				libraryName = "stdlib";
				break;
			case "assert":
				libraryName = "asserts";
				break;
			default:
			}
		}
		return new CommonSystemFunction(source, name, parameters, returnType,
				containingScope, containingScope.numFunctions(),
				(Location) null, this, libraryName);
	}

	@Override
	public CIVLSource systemSource() {
		return systemSource;
	}

	@Override
	public Variable variable(CIVLSource source, CIVLType type, Identifier name,
			int vid) {
		Variable variable = new CommonVariable(source, type, name, vid);

		if (name.name().equals(CIVL_FILESYSTEM_NAME)) {
			this.civlFilesystemVariableExpression = this.variableExpression(
					source, variable);
		}
		return variable;
	}

	@Override
	public SymbolicExpression processValue(int pid) {
		SymbolicExpression result;

		if (pid == -2)
			return this.nullProcessValue;
		if (pid < 0)
			return undefinedProcessValue;
		while (pid >= processValues.size())
			processValues.addAll(nullList);
		result = processValues.get(pid);
		if (result == null) {
			result = universe.canonic(universe.tuple(
					typeFactory.processSymbolicType,
					new Singleton<SymbolicExpression>(universe.integer(pid))));
			processValues.set(pid, result);
		}
		return result;
	}

	@Override
	public int getProcessId(CIVLSource source, SymbolicExpression processValue) {
		return extractIntField(source, processValue, zeroObj);
	}

	@Override
	public SymbolicExpression scopeValue(int sid) {
		SymbolicExpression result;

		if (sid == -2)
			return this.nullScopeValue;
		if (sid < 0)
			return this.undefinedScopeValue;
		while (sid >= scopeValues.size())
			scopeValues.addAll(nullList);
		result = scopeValues.get(sid);
		if (result == null) {
			result = universe.canonic(universe.tuple(
					typeFactory.scopeSymbolicType,
					new Singleton<SymbolicExpression>(universe.integer(sid))));
			scopeValues.set(sid, result);
		}
		return result;
	}

	@Override
	public void setSystemScope(Scope scope) {
		this.systemScope = scope;
	}

	@Override
	public int getScopeId(CIVLSource source, SymbolicExpression scopeValue) {
		return extractIntField(source, scopeValue, zeroObj);
	}

	/* *************************** Private Methods ************************* */

	@Override
	public SymbolicExpression undefinedValue(SymbolicType type) {
		if (type.equals(typeFactory.processSymbolicType))
			return this.undefinedProcessValue;
		else if (type.equals(typeFactory.scopeSymbolicType))
			return this.undefinedScopeValue;
		else {
			SymbolicExpression result = universe.symbolicConstant(
					universe.stringObject("UNDEFINED"), type);

			result = universe.canonic(result);
			return result;
		}
	}

	@Override
	public ArrayLiteralExpression arrayLiteralExpression(CIVLSource source,
			CIVLArrayType arrayType, List<Expression> elements) {
		return new CommonArrayLiteralExpression(source, joinScope(elements),
				getLowerScope(elements), arrayType, elements);
	}

	@Override
	public StructOrUnionLiteralExpression structOrUnionLiteralExpression(
			CIVLSource source, CIVLType structType, List<Expression> fields) {
		return new CommonStructOrUnionLiteralExpression(source,
				joinScope(fields), getLowerScope(fields), structType, fields);
	}

	@Override
	public StructOrUnionLiteralExpression structOrUnionLiteralExpression(
			CIVLSource source, Scope exprScope, CIVLType structType,
			SymbolicExpression constantValue) {
		return new CommonStructOrUnionLiteralExpression(source, exprScope,
				exprScope, structType, constantValue);
	}

	@Override
	public CharLiteralExpression charLiteralExpression(CIVLSource sourceOf,
			char value) {
		return new CommonCharLiteralExpression(sourceOf, typeFactory.charType,
				value);
	}

	@Override
	public Variable newAnonymousVariableForArrayLiteral(CIVLSource sourceOf,
			CIVLArrayType type) {
		String name = ModelConfiguration.ANONYMOUS_VARIABLE_PREFIX
				+ this.anonymousVariableId++;
		Variable variable = this.variable(sourceOf, type,
				this.identifier(sourceOf, name),
				this.systemScope.numVariables());

		variable.setConst(true);
		this.systemScope.addVariable(variable);
		return variable;
	}

	@Override
	public Variable newAnonymousVariable(CIVLSource sourceOf, Scope scope,
			CIVLType type) {
		String name = ModelConfiguration.ANONYMOUS_VARIABLE_PREFIX
				+ this.anonymousVariableId++;
		Variable variable = this.variable(sourceOf, type,
				this.identifier(sourceOf, name), scope.numVariables());

		scope.addVariable(variable);
		return variable;
	}

	// @Override
	// public Scope currentScope() {
	// return this.currentScope;
	// }

	@Override
	public Fragment anonFragment() {
		return this.anonFragment;
	}

	@Override
	public void clearAnonFragment() {
		this.anonFragment = new CommonFragment();
	}

	@Override
	public void addAnonStatement(Statement statement) {
		this.anonFragment.addNewStatement(statement);
	}

	@Override
	public Expression systemGuardExpression(CallOrSpawnStatement call) {
		SystemGuardExpression systemGuard = new CommonSystemGuardExpression(
				call.getSource(), call.statementScope(),
				((SystemFunction) call.function()).getLibrary(), call
						.function().name().name(), call.arguments(),
				typeFactory.booleanType);

		if (this.isTrue(call.guard()))
			return systemGuard;
		return this.binaryExpression(call.guard().getSource(),
				BINARY_OPERATOR.AND, call.guard(), systemGuard);
	}

	@Override
	public Expression functionGuardExpression(CIVLSource source,
			Expression function, List<Expression> arguments) {
		FunctionGuardExpression functionGuard = new CommonFunctionGuardExpression(
				source, function, arguments, typeFactory.booleanType);

		return functionGuard;
	}

	@Override
	public Model model() {
		return this.modelBuilder.getModel();
	}

	@Override
	public VariableExpression civlFilesystemVariableExpression() {
		return this.civlFilesystemVariableExpression;
	}

	@Override
	public boolean isPocessIdDefined(int pid) {
		if (pid == -1)
			return false;
		return true;
	}

	@Override
	public boolean isScopeIdDefined(int scopeId) {
		if (scopeId == -1)
			return false;
		return true;
	}

	@Override
	public boolean isProcNull(CIVLSource source, SymbolicExpression procValue) {
		int pid = extractIntField(source, procValue, zeroObj);

		return this.isProcessIdNull(pid);
	}

	@Override
	public Fragment civlForEnterFragment(CIVLSource source, Location src,
			Expression dom, List<Variable> variables, Variable counter) {
		DomainIteratorStatement statement = new CommonCivlForEnterStatement(
				source, src, this.trueExpression(source), dom, variables,
				counter);

		return new CommonFragment(statement);
	}

	@Override
	public RegularRangeExpression regularRangeExpression(CIVLSource source,
			Expression low, Expression high, Expression step) {
		return new CommonRegularRangeExpression(source,
				joinScope(Arrays.asList(low, high, step)),
				getLowerScope(Arrays.asList(low, high, step)),
				typeFactory.rangeType, low, high, step);
	}

	@Override
	public RecDomainLiteralExpression recDomainLiteralExpression(
			CIVLSource source, List<Expression> ranges, CIVLType type) {
		return new CommonRecDomainLiteralExpression(source,
				getLowerScope(ranges), ranges, type);
	}

	@Override
	public DomainGuardExpression domainGuard(CIVLSource source,
			List<Variable> vars, Variable counter, Expression domain) {
		return new CommonDomainGuardExpression(source, typeFactory.booleanType,
				domain, vars, counter);
	}

	@Override
	public VariableExpression domSizeVariable(CIVLSource source, Scope scope) {
		Variable variable = this.variable(
				source,
				typeFactory.integerType,
				this.identifier(source, DOM_SIZE_PREFIX
						+ this.domSizeVariableId++), scope.numVariables());

		scope.addVariable(variable);
		return this.variableExpression(source, variable);
	}

	@Override
	public Identifier getLiteralDomCounterIdentifier(CIVLSource source,
			int count) {
		return identifier(source, "__LiteralDomain_counter" + count + "__");
	}

	@Override
	public VariableExpression parProcsVariable(CIVLSource source,
			CIVLType type, Scope scope) {
		Variable variable = this.variable(
				source,
				type,
				this.identifier(source, PAR_PROC_PREFIX
						+ this.parProcsVariableId++), scope.numVariables());

		scope.addVariable(variable);
		return this.variableExpression(source, variable);
	}

	@Override
	public CivlParForSpawnStatement civlParForEnterStatement(CIVLSource source,
			Location location, Expression domain, VariableExpression domSize,
			VariableExpression procsVar, CIVLFunction parProcFunc) {
		return new CommonCivlParForSpawnStatement(source, location,
				this.trueExpression(source), domain, domSize, procsVar,
				parProcFunc);
	}

	@Override
	public FunctionIdentifierExpression waitallFunctionPointer() {
		if (this.waitallFuncPointer == null) {
			List<Variable> parameters = new ArrayList<>(2);
			CIVLFunction function;

			parameters.add(this.variable(systemSource,
					typeFactory.pointerType(typeFactory.processType),
					this.identifier(systemSource, "procs"), 1));
			parameters.add(this.variable(systemSource, typeFactory.integerType,
					this.identifier(systemSource, "num"), 2));
			function = this.systemFunction(systemSource,
					this.identifier(systemSource, "$waitall"), parameters,
					typeFactory.voidType, systemScope, "civlc");
			this.waitallFuncPointer = this.functionIdentifierExpression(
					systemSource, function);
		}
		return this.waitallFuncPointer;
	}

	@Override
	public boolean isProcessIdNull(int pid) {
		if (pid == -2)
			return true;
		return false;
	}

	@Override
	public ArraySliceReference arraySliceReference(ArraySliceKind sliceKind,
			Expression index) {
		return new CommonArraySliceReference(sliceKind, index);
	}

	@Override
	public SelfReference selfReference() {
		return new CommonSelfReference();
	}

	@Override
	public StructOrUnionFieldReference structFieldReference(int fieldIndex) {
		return new CommonStructOrUnionFieldReference(fieldIndex);
	}

	@Override
	public MemoryUnitExpression memoryUnitExpression(CIVLSource source,
			Variable variable, CIVLType objType, MemoryUnitReference reference,
			boolean writable, boolean hasPinterRef) {
		return new CommonMemoryUnitExpression(source, variable, objType,
				reference, writable, hasPinterRef);
	}

	@Override
	public CIVLTypeFactory typeFactory() {
		return this.typeFactory;
	}

	/* *************************** Private Methods ************************* */

	/**
	 * An atomic lock variable is used to keep track of the process that
	 * executes an $atomic block which prevents interleaving with other
	 * processes. This variable is maintained as a global variable
	 * {@link ComonModelFactory#ATOMIC_LOCK_VARIABLE} of <code>$proc</code> type
	 * in the root scope in the CIVL model (always with index 0).
	 * 
	 * @param scope
	 *            The scope of the atomic lock variable, and should always be
	 *            the root scope.
	 */
	private void createAtomicLockVariable(Scope scope) {
		// Since the atomic lock variable is not declared explicitly in the CIVL
		// model specification, the system source will be used here.
		Variable variable = this.variable(this.systemSource,
				typeFactory.processType, this.identifier(this.systemSource,
						ModelConfiguration.ATOMIC_LOCK_VARIABLE), scope
						.numVariables());

		this.atomicLockVariableExpression = this.variableExpression(
				this.systemSource, variable);
		scope.addVariable(variable);
	}

	private void createTimeVariables(Scope scope) {
		// Since the atomic lock variable is not declared explicitly in the CIVL
		// model specification, the system source will be used here.
		if (modelBuilder.hasNextTimeCountCall) {
			timeCountVariable = this.variable(this.systemSource,
					typeFactory.integerType, this.identifier(this.systemSource,
							ModelConfiguration.TIME_COUNT_VARIABLE), scope
							.numVariables());
			timeCountVariable.setStatic(true);
			scope.addVariable(timeCountVariable);
		}
		if (modelBuilder.timeLibIncluded) {
			brokenTimeVariable = this.variable(this.systemSource,
					typeFactory.integerType, this.identifier(systemSource,
							ModelConfiguration.BROKEN_TIME_VARIABLE), scope
							.numVariables());
			scope.addVariable(brokenTimeVariable);
		}
	}

	private void createSymbolicConstantCounter(Scope scope) {
		Variable symbolicConstantCounter = this.variable(this.systemSource,
				typeFactory.integerType, this.identifier(this.systemSource,
						ModelConfiguration.SYMBOLIC_CONSTANT_COUNTER), scope
						.numVariables());

		scope.addVariable(symbolicConstantCounter);
	}

	private void createSymbolicInputCounter(Scope scope) {
		Variable symbolicInputCounter = this.variable(this.systemSource,
				typeFactory.integerType, this.identifier(this.systemSource,
						ModelConfiguration.SYMBOLIC_INPUT_COUNTER), scope
						.numVariables());

		scope.addVariable(symbolicInputCounter);
	}

	/* *************************** Private Methods ************************* */

	/**
	 * Gets a Java concrete int from a symbolic expression or throws exception.
	 * 
	 * @param source
	 * 
	 * @param expression
	 *            a numeric expression expected to hold concrete int value
	 * @return the concrete int
	 * @throws CIVLInternalException
	 *             if a concrete integer value cannot be extracted
	 */
	private int extractInt(CIVLSource source, NumericExpression expression) {
		IntegerNumber result = (IntegerNumber) universe
				.extractNumber(expression);

		if (result == null)
			throw new CIVLInternalException(
					"Unable to extract concrete int from " + expression, source);
		return result.intValue();
	}

	/**
	 * Gets a concrete Java int from the field of a symbolic expression of tuple
	 * type or throws exception.
	 * 
	 * @param source
	 * 
	 * @param tuple
	 *            symbolic expression of tuple type
	 * @param fieldIndex
	 *            index of a field in that tuple
	 * @return the concrete int value of that field
	 */
	private int extractIntField(CIVLSource source, SymbolicExpression tuple,
			IntObject fieldIndex) {
		NumericExpression field = (NumericExpression) universe.tupleRead(tuple,
				fieldIndex);

		return extractInt(source, field);
	}

	/**
	 * @param s0
	 *            A scope. May be null.
	 * @param s1
	 *            A scope. May be null.
	 * @return The scope that is the join, or least common ancestor in the scope
	 *         tree, of s0 and s1. Null if both are null. If exactly one of s0
	 *         and s1 are null, returns the non-null scope.
	 */
	private Scope join(Scope s0, Scope s1) {
		Set<Scope> s0Ancestors = new HashSet<Scope>();
		Scope s0Ancestor = s0;
		Scope s1Ancestor = s1;

		if (s0 == null) {
			return s1;
		} else if (s1 == null) {
			return s0;
		}
		s0Ancestors.add(s0Ancestor);
		while (s0Ancestor.parent() != null) {
			s0Ancestor = s0Ancestor.parent();
			s0Ancestors.add(s0Ancestor);
		}
		while (true) {
			if (s0Ancestors.contains(s1Ancestor)) {
				return s1Ancestor;
			}
			s1Ancestor = s1Ancestor.parent();
		}
	}

	/**
	 * Returns the lower scope. Precondition: one of the scope must be the
	 * ancestor of the other if they are not the same.
	 * 
	 * @param s0
	 * @param s1
	 * @return
	 */
	private Scope getLower(Scope s0, Scope s1) {
		if (s0 == null)
			return s1;
		if (s1 == null)
			return s0;
		if (s0.id() != s1.id()) {
			Scope sParent0 = s0, sParent1 = s1;

			while (sParent0.id() > 0 && sParent1.id() > 0) {
				sParent0 = sParent0.parent();
				sParent1 = sParent1.parent();
			}
			if (sParent0.id() == 0)
				return s1;
			return s0;
		}
		return s0;
	}

	private Scope getLowerScope(List<Expression> expressions) {
		Scope scope = null;

		for (Expression expression : expressions) {
			if (expression != null)
				scope = getLower(scope, expression.lowestScope());
		}
		return scope;
	}

	/**
	 * Calculate the join scope (the most local common scope) of a list of
	 * expressions.
	 * 
	 * @param expressions
	 *            The list of expressions whose join scope is to be computed.
	 * @return The join scope of the list of expressions.
	 */
	private Scope joinScope(List<Expression> expressions) {
		Scope scope = null;

		for (Expression expression : expressions) {
			scope = join(scope, expression.expressionScope());
		}
		return scope;
	}

	/**
	 * 
	 * @return The size of the top conditional expression queue
	 */
	private int sizeofTopConditionalExpressionQueue() {
		if (conditionalExpressions.isEmpty())
			return 0;
		return conditionalExpressions.peek().size();
	}

	/**
	 * Generate a temporal variable for translating away conditional expression
	 * 
	 * @param kind
	 *            The temporal variable kind
	 * @param scope
	 *            The scope of the temporal variable
	 * @param source
	 *            The CIVL source of the conditional expression
	 * @param type
	 *            The CIVL type of the conditional expression
	 * @return The variable expression referring to the temporal variable
	 */
	private VariableExpression tempVariable(TempVariableKind kind, Scope scope,
			CIVLSource source, CIVLType type) {
		String name = "";
		int vid = scope.numVariables();
		StringObject stringObject;
		Variable variable;
		VariableExpression result;

		switch (kind) {
		case CONDITIONAL:
			name = CONDITIONAL_VARIABLE_PREFIX
					+ this.conditionalExpressionCounter++;
			break;
		default:
		}
		stringObject = (StringObject) universe.canonic(universe
				.stringObject(name));
		variable = new CommonVariable(source, type, new CommonIdentifier(
				source, stringObject), vid);
		result = new CommonVariableExpression(source, variable);
		scope.addVariable(variable);
		return result;
	}

	/**
	 * @return The earliest conditional expression in the latest queue in the
	 *         stack of conditional expression queues
	 */
	private ConditionalExpression pollFirstConditionaExpression() {
		return conditionalExpressions.peek().pollFirst();
	}

	@Override
	public List<CodeAnalyzer> codeAnalyzers() {
		return this.codeAnalyzers;
	}

	@Override
	public void setCodeAnalyzers(List<CodeAnalyzer> analyzers) {
		this.codeAnalyzers = analyzers;
	}

	@Override
	public List<Variable> inputVariables() {
		return this.inputVariables;
	}

	@Override
	public void addInputVariable(Variable variable) {
		this.inputVariables.add(variable);
	}

	@Override
	public FunctionIdentifierExpression elaborateDomainPointer() {
		if (this.elaborateDomainFuncPointer == null) {
			List<Variable> parameters = new ArrayList<>(2);
			CIVLFunction function;

			parameters.add(this.variable(systemSource,
					typeFactory.domainType(),
					this.identifier(systemSource, "domain"), 1));
			function = this.systemFunction(systemSource,
					this.identifier(systemSource, "$elaborate_domain"),
					parameters, typeFactory.voidType, systemScope, "civlc");
			this.elaborateDomainFuncPointer = this
					.functionIdentifierExpression(systemSource, function);
		}
		return this.elaborateDomainFuncPointer;
	}

	@Override
	public NoopStatement noopStatementTemporary(CIVLSource civlSource,
			Location source) {
		return new CommonNoopStatement(civlSource, source,
				this.trueExpression(civlSource), true);
	}

	@Override
	public NoopStatement noopStatementForVariableDeclaration(
			CIVLSource civlSource, Location source) {
		return new CommonNoopStatement(civlSource, source,
				this.trueExpression(civlSource), false, true);
	}

	@Override
	public WildcardExpression wildcardExpression(CIVLSource source,
			CIVLType type) {
		return new CommonWildcardExpression(source, type);
	}

	@Override
	public Nothing nothing(CIVLSource source) {
		return new CommonNothing(source);
	}

	@Override
	public PointerSetExpression pointerSetExpression(CIVLSource source,
			Scope scope, LHSExpression basePointer, Expression range) {
		Scope expressionScope;
		Scope lowestScope;

		if (range != null) {
			expressionScope = join(basePointer.expressionScope(),
					range.expressionScope());
			lowestScope = getLower(basePointer.lowestScope(),
					range.lowestScope());
		} else {
			expressionScope = basePointer.expressionScope();
			lowestScope = basePointer.lowestScope();
		}
		expressionScope = join(scope, expressionScope);
		lowestScope = getLower(scope, lowestScope);
		return new CommonPointerSetExpression(source, expressionScope,
				lowestScope, typeFactory.incompleteArrayType(basePointer
						.getExpressionType()), basePointer, range);
	}

	@Override
	public ContractVerifyStatement contractVerifyStatement(
			CIVLSource civlSource, Scope scope, Location source,
			FunctionIdentifierExpression functionExpression,
			List<Expression> arguments) {
		Scope lowestScope = functionExpression.lowestScope();
		Expression guard;

		for (Expression arg : arguments)
			lowestScope = this.getLower(scope, arg.lowestScope());
		guard = this.trueExpression(null);
		return new CommonContractVerifyStatement(civlSource, scope,
				lowestScope, source, functionExpression, arguments, guard);
	}

	@Override
	public MPIContractExpression mpiContractExpression(CIVLSource source,
			Scope scope, Expression communicator, Expression[] arguments,
			MPI_CONTRACT_EXPRESSION_KIND kind) {
		Scope lowestScope = getLower(communicator.lowestScope(), scope);
		CIVLType type;

		for (int i = 0; i < arguments.length; i++)
			lowestScope = getLower(arguments[i].lowestScope(), lowestScope);
		switch (kind) {
		case MPI_EQUALS:
		case MPI_EMPTY_IN:
		case MPI_EMPTY_OUT:
			type = typeFactory.booleanType;
			break;
		case MPI_SIZE:
			type = typeFactory.integerType;
			break;
		case MPI_REGION: // location type or $mem type in fact
			type = typeFactory.voidType;
			break;
		default:
			throw new CIVLInternalException("unreachable", source);

		}
		return new CommonMPIContractExpression(source, scope, lowestScope,
				type, kind, communicator, arguments);
	}
}
