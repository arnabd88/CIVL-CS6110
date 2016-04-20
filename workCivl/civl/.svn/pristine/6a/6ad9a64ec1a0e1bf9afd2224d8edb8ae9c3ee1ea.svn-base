package edu.udel.cis.vsl.civl.model.common;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import edu.udel.cis.vsl.abc.ast.entity.IF.Function;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.token.IF.CToken;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.TokenFactory;
import edu.udel.cis.vsl.civl.err.CIVLException;
import edu.udel.cis.vsl.civl.err.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.AbstractFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Fragment;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.Model;
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
import edu.udel.cis.vsl.civl.model.IF.expression.DotExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DynamicTypeOfExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.FunctionGuardExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.FunctionPointerExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.HereOrRootExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.InitialValueExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.IntegerLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ProcnullExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.QuantifiedExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.QuantifiedExpression.Quantifier;
import edu.udel.cis.vsl.civl.model.IF.expression.RealLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ResultExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ScopeofExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SelfExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SizeofExpressionExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SizeofTypeExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.StructOrUnionLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SubscriptExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SystemFunctionCallExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SystemGuardExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression.UNARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.WaitGuardExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.AssertStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.AssignStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.AssumeStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ChooseStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.MallocStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.NoopStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ReturnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.statement.WaitStatement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLBundleType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLCompleteArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLEnumType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLFunctionType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLHeapType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPointerType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPrimitiveType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPrimitiveType.PrimitiveTypeKind;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLStructOrUnionType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.type.StructOrUnionField;
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
import edu.udel.cis.vsl.civl.model.common.expression.CommonDotExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonDynamicTypeOfExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonFunctionGuardExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonFunctionPointerExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonHereOrRootExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonInitialValueExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonIntegerLiteralExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonProcnullExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonQuantifiedExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonRealLiteralExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonResultExpression;
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
import edu.udel.cis.vsl.civl.model.common.expression.CommonWaitGuardExpression;
import edu.udel.cis.vsl.civl.model.common.location.CommonLocation;
import edu.udel.cis.vsl.civl.model.common.statement.CommonAssertStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonAssignStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonAssumeStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonAtomBranchStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonAtomicLockAssignStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonCallStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonChooseStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonGotoBranchStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonIfElseBranchStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonLoopBranchStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonMallocStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonNoopStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonReturnStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonSwitchBranchStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonWaitStatement;
import edu.udel.cis.vsl.civl.model.common.statement.StatementSet;
import edu.udel.cis.vsl.civl.model.common.type.CommonArrayType;
import edu.udel.cis.vsl.civl.model.common.type.CommonBundleType;
import edu.udel.cis.vsl.civl.model.common.type.CommonCompleteArrayType;
import edu.udel.cis.vsl.civl.model.common.type.CommonEnumType;
import edu.udel.cis.vsl.civl.model.common.type.CommonFunctionType;
import edu.udel.cis.vsl.civl.model.common.type.CommonHeapType;
import edu.udel.cis.vsl.civl.model.common.type.CommonPointerType;
import edu.udel.cis.vsl.civl.model.common.type.CommonPrimitiveType;
import edu.udel.cis.vsl.civl.model.common.type.CommonStructField;
import edu.udel.cis.vsl.civl.model.common.type.CommonStructOrUnionType;
import edu.udel.cis.vsl.civl.model.common.variable.CommonVariable;
import edu.udel.cis.vsl.civl.util.Pair;
import edu.udel.cis.vsl.civl.util.Singleton;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicUnionType;

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
	 * expressions, choose_int function calls that require to temporal variable
	 * to store some intermediate data
	 * 
	 */
	public enum TempVariableKind {
		CONDITIONAL, CHOOSE
	}

	/* *************************** Static Fields *************************** */

	/**
	 * The name of the atomic lock variable
	 */
	private static final String ATOMIC_LOCK_VARIABLE = "__atomic_lock_var";

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
	private static final String CONDITIONAL_VARIABLE_PREFIX = "__cond_var_";

	private static final String ANONYMOUS_VARIABLE_PREFIX = "__anon_";

	private static final String HEAP_VAR = "__heap";

	/* ************************** Instance Fields ************************** */

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

	/**
	 * The unique boolean type used in the system.
	 */
	private CIVLPrimitiveType booleanType;

	private CIVLBundleType bundleType;

	private SymbolicUnionType bundleSymbolicType;

	/**
	 * The unique char type used in the system.
	 */
	private CIVLPrimitiveType charType;

	/**
	 * TODO Why do we need an ID for each ChooseStatement?
	 */
	private int chooseID = 0;

	/**
	 * The number of conditional expressions that have been encountered, used to
	 * create temporal variable.
	 */
	private int conditionalExpressionCounter = 0;

	/**
	 * The stack of queues of conditional expression.
	 */
	private Stack<ArrayDeque<ConditionalExpression>> conditionalExpressions;

	private Scope currentScope;

	/**
	 * The unique dynamic symbolic type used in the system.
	 */
	private SymbolicTupleType dynamicSymbolicType;

	/**
	 * The unique dynamic type used in the system.
	 */
	private CIVLPrimitiveType dynamicType;

	/** Keep a set of used identifiers for fly-weighting purposes. */
	private Map<String, Identifier> identifiers;

	/**
	 * The unique integer type used in the system.
	 */
	private CIVLPrimitiveType integerType;

	/**
	 * The unique heap type
	 */
	private CIVLHeapType heapType;

	/**
	 * The unique symbolic heap type
	 */
	private SymbolicTupleType heapSymbolicType;

	/**
	 * The map of handled object types and their field ID in the heap type.
	 */
	private Map<CIVLType, Integer> heapFieldTypeMap = new HashMap<>();

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

	/** A list of nulls of length CACHE_INCREMENT */
	private List<SymbolicExpression> nullList = new LinkedList<SymbolicExpression>();

	/**
	 * The unique symbolic pointer type used in the system.
	 */
	private SymbolicTupleType pointerSymbolicType;

	/**
	 * The unique symbolic function pointer type used in the system.
	 */
	private SymbolicTupleType functionPointerSymbolicType;

	/**
	 * The unique symbolic process type used in the system.
	 */
	private SymbolicTupleType processSymbolicType;

	/**
	 * The unique process type used in the system.
	 */
	private CIVLPrimitiveType processType;

	/**
	 * The list of canonicalized symbolic expressions of process IDs, will be
	 * used in Executor, Evaluator and State factory to obtain symbolic process
	 * ID's.
	 */
	private ArrayList<SymbolicExpression> processValues = new ArrayList<SymbolicExpression>();

	/**
	 * The unique real type used in the system.
	 */
	private CIVLPrimitiveType realType;

	/**
	 * The unique symbolic scope type used in the system.
	 */
	private SymbolicTupleType scopeSymbolicType;

	/** Keep a unique number to identify scopes. */
	private int scopeID = 0;

	/**
	 * The unique scope type used in the system.
	 */
	private CIVLPrimitiveType scopeType;

	/**
	 * The list of canonicalized symbolic expressions of scope IDs, will be used
	 * in Executor, Evaluator and State factory to obtain symbolic scope ID's.
	 */
	private ArrayList<SymbolicExpression> scopeValues = new ArrayList<SymbolicExpression>();

	/**
	 * The unique symbolic string type used in the system.
	 */
	private SymbolicArrayType stringSymbolicType;

	/**
	 * The unique string type used in the system.
	 */
	private CIVLPrimitiveType stringType;

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
	 * The unique void type used in the system.
	 */
	private CIVLPrimitiveType voidType;

	/**
	 * The unique integer object of zero.
	 */
	private IntObject zeroObj;

	/**
	 * The system scope of the model, i.e., the root scope.
	 */
	private Scope systemScope;

	/* **************************** Constructors *************************** */

	/**
	 * The factory to create all model components. Usually this is the only way
	 * model components will be created.
	 * 
	 * @param universe
	 *            The symbolic universe
	 */
	public CommonModelFactory(SymbolicUniverse universe) {
		Iterable<SymbolicType> intTypeSingleton = new Singleton<SymbolicType>(
				universe.integerType());
		LinkedList<SymbolicType> pointerComponents = new LinkedList<>();
		LinkedList<SymbolicType> fpointerComponents = new LinkedList<>();

		this.universe = universe;
		this.voidType = primitiveType(PrimitiveTypeKind.VOID, null);
		this.integerType = primitiveType(PrimitiveTypeKind.INT,
				universe.integerType());
		this.booleanType = primitiveType(PrimitiveTypeKind.BOOL,
				universe.booleanType());
		this.realType = primitiveType(PrimitiveTypeKind.REAL,
				universe.realType());
		this.charType = primitiveType(PrimitiveTypeKind.CHAR,
				universe.characterType());
		this.identifiers = new HashMap<String, Identifier>();
		scopeSymbolicType = (SymbolicTupleType) universe.canonic(universe
				.tupleType(universe.stringObject("scope"), intTypeSingleton));
		scopeType = primitiveType(PrimitiveTypeKind.SCOPE, scopeSymbolicType);
		processSymbolicType = (SymbolicTupleType) universe.canonic(universe
				.tupleType(universe.stringObject("process"), intTypeSingleton));
		processType = primitiveType(PrimitiveTypeKind.PROCESS,
				processSymbolicType);
		dynamicSymbolicType = (SymbolicTupleType) universe.canonic(universe
				.tupleType(universe.stringObject("dynamicType"),
						intTypeSingleton));
		dynamicType = primitiveType(PrimitiveTypeKind.DYNAMIC,
				dynamicSymbolicType);
		pointerComponents.add(scopeType.getDynamicType(universe));
		pointerComponents.add(universe.integerType());
		pointerComponents.add(universe.referenceType());
		pointerSymbolicType = (SymbolicTupleType) universe
				.canonic(universe.tupleType(universe.stringObject("pointer"),
						pointerComponents));
		fpointerComponents.add(scopeType.getDynamicType(universe));
		fpointerComponents.add(universe.arrayType(universe.characterType()));
		functionPointerSymbolicType = (SymbolicTupleType) universe
				.canonic(universe.tupleType(universe.stringObject("fpointer"),
						fpointerComponents));
		stringSymbolicType = (SymbolicArrayType) universe.canonic(universe
				.arrayType(universe.characterType()));
		stringType = primitiveType(PrimitiveTypeKind.STRING, stringSymbolicType);
		zeroObj = (IntObject) universe.canonic(universe.intObject(0));
		for (int i = 0; i < CACHE_INCREMENT; i++)
			nullList.add(null);
		undefinedProcessValue = universe.canonic(universe.tuple(
				processSymbolicType,
				new Singleton<SymbolicExpression>(universe.integer(-1))));
		this.nullProcessValue = universe.canonic(universe.tuple(
				processSymbolicType,
				new Singleton<SymbolicExpression>(universe.integer(-2))));
		undefinedScopeValue = universe.canonic(universe.tuple(
				scopeSymbolicType,
				new Singleton<SymbolicExpression>(universe.integer(-1))));
		this.nullScopeValue = universe.canonic(universe.tuple(
				scopeSymbolicType,
				new Singleton<SymbolicExpression>(universe.integer(-2))));
		this.conditionalExpressions = new Stack<ArrayDeque<ConditionalExpression>>();
		this.anonFragment = new CommonFragment();
	}

	/* ********************** Methods from ModelFactory ******************** */

	/* *********************************************************************
	 * CIVL Types
	 * *********************************************************************
	 */

	@Override
	public void addHeapFieldType(CIVLType type, int id) {
		this.heapFieldTypeMap.put(type, id);
	}

	@Override
	public int getHeapFieldId(CIVLType type) {
		if (this.heapFieldTypeMap.containsKey(type))
			return heapFieldTypeMap.get(type);
		return -1;
	}

	@Override
	public CIVLPrimitiveType booleanType() {
		return booleanType;
	}

	@Override
	public void completeHeapType(CIVLHeapType heapType,
			Collection<MallocStatement> mallocs) {
		SymbolicTupleType dynamicType = computeDynamicHeapType(mallocs);
		SymbolicExpression initialValue = computeInitialHeapValue(dynamicType);
		SymbolicExpression undefinedValue = universe.symbolicConstant(
				universe.stringObject("UNDEFINED"), dynamicType);

		undefinedValue = universe.canonic(undefinedValue);
		heapType.complete(mallocs, dynamicType, initialValue, undefinedValue);
		this.heapType = heapType;
		this.heapSymbolicType = dynamicType;
	}

	@Override
	public CIVLPrimitiveType charType() {
		return charType;
	}

	@Override
	public CIVLCompleteArrayType completeArrayType(CIVLType elementType,
			Expression extent) {
		return new CommonCompleteArrayType(elementType, extent);
	}

	@Override
	public CIVLPrimitiveType dynamicType() {
		return dynamicType;
	}

	@Override
	public CIVLEnumType enumType(String name, Map<String, BigInteger> valueMap) {
		return new CommonEnumType(name, valueMap, universe.integerType());
	}

	@Override
	public CIVLFunctionType functionType(CIVLType returnType,
			CIVLType[] paraTypes) {
		return new CommonFunctionType(returnType, paraTypes);
	}

	@Override
	public CIVLHeapType heapType(String name) {
		return new CommonHeapType(name);
	}

	@Override
	public CIVLArrayType incompleteArrayType(CIVLType baseType) {
		return new CommonArrayType(baseType);
	}

	@Override
	public CIVLPrimitiveType integerType() {
		return integerType;
	}

	@Override
	public CIVLBundleType newBundleType() {
		return new CommonBundleType();
	}

	@Override
	public CIVLPointerType pointerType(CIVLType baseType) {
		return new CommonPointerType(baseType, pointerSymbolicType);
	}

	@Override
	public CIVLPrimitiveType processType() {
		return processType;
	}

	@Override
	public CIVLPrimitiveType realType() {
		return realType;
	}

	@Override
	public CIVLPrimitiveType scopeType() {
		return scopeType;
	}

	@Override
	public CIVLPrimitiveType stringType() {
		return stringType;
	}

	@Override
	public CIVLStructOrUnionType structOrUnionType(Identifier name,
			boolean isStruct) {
		return new CommonStructOrUnionType(name, isStruct);
	}

	@Override
	public CIVLPrimitiveType voidType() {
		return voidType;
	}

	/* *********************************************************************
	 * SARL symbolic types
	 * *********************************************************************
	 */

	@Override
	public SymbolicTupleType dynamicSymbolicType() {
		return dynamicSymbolicType;
	}

	@Override
	public SymbolicTupleType functionPointerSymbolicType() {
		return functionPointerSymbolicType;
	}

	@Override
	public SymbolicTupleType pointerSymbolicType() {
		return pointerSymbolicType;
	}

	@Override
	public SymbolicTupleType processSymbolicType() {
		return processSymbolicType;
	}

	@Override
	public SymbolicTupleType scopeSymbolicType() {
		return scopeSymbolicType;
	}

	@Override
	public SymbolicArrayType stringSymbolicType() {
		return stringSymbolicType;
	}

	/* *********************************************************************
	 * CIVL Expressions
	 * *********************************************************************
	 */

	@Override
	public AbstractFunctionCallExpression abstractFunctionCallExpression(
			CIVLSource source, AbstractFunction function,
			List<Expression> arguments) {
		CommonAbstractFunctionCallExpression result = new CommonAbstractFunctionCallExpression(
				source, function, arguments);
		Scope expressionScope = null;

		// Note: While the abstract function may be declared in e.g. the
		// outermost scope, since it has no value or state, it doesn't
		// contribute anything non-local to the expression scope.
		expressionScope = joinScope(arguments);
		result.setExpressionScope(expressionScope);
		result.setExpressionType(function.returnType());
		return result;
	}

	@Override
	public AddressOfExpression addressOfExpression(CIVLSource source,
			LHSExpression operand) {
		AddressOfExpression result = new CommonAddressOfExpression(source,
				operand);

		result.setExpressionScope(operand.expressionScope());
		((CommonExpression) result).setExpressionType(this.pointerType(operand
				.getExpressionType()));
		return result;
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
		BinaryExpression result = new CommonBinaryExpression(source, operator,
				left, right);

		result.setExpressionScope(join(left.expressionScope(),
				right.expressionScope()));
		switch (operator) {
		case AND:
		case EQUAL:
		case LESS_THAN:
		case LESS_THAN_EQUAL:
		case NOT_EQUAL:
		case OR:
			((CommonBinaryExpression) result).setExpressionType(booleanType);
			break;
		case PLUS:
		case TIMES:
		case DIVIDE:
		case MINUS:
		case MODULO:
		default:
			CIVLType leftType = left.getExpressionType();
			CIVLType rightType = right.getExpressionType();

			// Types should be the same unless we're doing pointer arithmetic.
			if (leftType.equals(rightType)) {
				((CommonBinaryExpression) result).setExpressionType(leftType);
			} else if (leftType instanceof CIVLPointerType
					&& rightType instanceof CIVLPrimitiveType) {
				assert ((CIVLPrimitiveType) rightType).primitiveTypeKind() == PrimitiveTypeKind.INT;
				((CommonBinaryExpression) result).setExpressionType(leftType);
			} else if (leftType instanceof CIVLPointerType
					&& rightType instanceof CIVLPrimitiveType) {
				assert ((CIVLPrimitiveType) rightType).primitiveTypeKind() == PrimitiveTypeKind.INT;
				((CommonBinaryExpression) result).setExpressionType(leftType);
			} else
				throw new CIVLException("Incompatible types to +", source);
			break;
		}
		return result;
	}

	@Override
	public Expression booleanExpression(Expression expression) {
		CIVLSource source = expression.getSource();

		if (!expression.getExpressionType().equals(booleanType())) {
			if (expression.getExpressionType().equals(integerType())) {
				expression = binaryExpression(source,
						BINARY_OPERATOR.NOT_EQUAL, expression,
						integerLiteralExpression(source, BigInteger.ZERO));
			} else if (expression.getExpressionType().equals(realType())) {
				expression = binaryExpression(source,
						BINARY_OPERATOR.NOT_EQUAL, expression,
						realLiteralExpression(source, BigDecimal.ZERO));
			} else if (expression.getExpressionType().isPointerType()) {
				CIVLPointerType pointerType = (CIVLPointerType) expression
						.getExpressionType();

				expression = binaryExpression(source,
						BINARY_OPERATOR.NOT_EQUAL, expression,
						this.nullPointerExpression(pointerType, source));
			} else {
				throw new CIVLInternalException(
						"Unable to convert expression to boolean type", source);
			}
		}
		return expression;
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
		CommonBooleanLiteralExpression result;

		result = new CommonBooleanLiteralExpression(source, value);
		result.setExpressionType(booleanType);
		return result;
	}

	@Override
	public BoundVariableExpression boundVariableExpression(CIVLSource source,
			Identifier name, CIVLType type) {
		CommonBoundVariableExpression result = new CommonBoundVariableExpression(
				source, name);

		result.setExpressionType(type);
		return result;
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
		ConditionalExpression result = new CommonConditionalExpression(source,
				condition, trueBranch, falseBranch);

		result.setExpressionScope(join(
				condition.expressionScope(),
				join(trueBranch.expressionScope(),
						falseBranch.expressionScope())));
		assert trueBranch.getExpressionType().equals(
				falseBranch.getExpressionType());
		((CommonConditionalExpression) result).setExpressionType(trueBranch
				.getExpressionType());
		return result;
	}

	@Override
	public CastExpression castExpression(CIVLSource source, CIVLType type,
			Expression expression) {
		CastExpression result = new CommonCastExpression(source, type,
				expression);

		result.setExpressionScope(expression.expressionScope());
		((CommonCastExpression) result).setExpressionType(type);
		return result;
	}

	@Override
	public DereferenceExpression dereferenceExpression(CIVLSource source,
			Expression pointer) {
		CIVLPointerType pointerType = (CIVLPointerType) pointer
				.getExpressionType();
		DereferenceExpression result = new CommonDereferenceExpression(source,
				pointer);

		result.setExpressionScope(this.systemScope); // indicates unknown scope
		((CommonExpression) result).setExpressionType(pointerType.baseType());
		return result;
	}

	@Override
	public DerivativeCallExpression derivativeCallExpression(CIVLSource source,
			AbstractFunction function,
			List<Pair<Variable, IntegerLiteralExpression>> partials,
			List<Expression> arguments) {
		CommonDerivativeCallExpression result = new CommonDerivativeCallExpression(
				source, function, partials, arguments);
		Scope expressionScope = null;

		for (Expression arg : arguments) {
			expressionScope = join(expressionScope, arg.expressionScope());
		}
		result.setExpressionScope(expressionScope);
		result.setExpressionType(function.returnType());
		return result;
	}

	@Override
	public DotExpression dotExpression(CIVLSource source, Expression struct,
			int fieldIndex) {
		CommonDotExpression result = new CommonDotExpression(source, struct,
				fieldIndex);
		CIVLType structType = struct.getExpressionType();

		result.setExpressionScope(struct.expressionScope());
		assert structType instanceof CIVLStructOrUnionType;
		result.setExpressionType(((CIVLStructOrUnionType) structType).getField(
				fieldIndex).type());
		return result;
	}

	@Override
	public DynamicTypeOfExpression dynamicTypeOfExpression(CIVLSource source,
			CIVLType type) {
		CommonDynamicTypeOfExpression result = new CommonDynamicTypeOfExpression(
				source, type);

		// result.setExpressionScope(expressionScope)
		result.setExpressionType(dynamicType);
		return result;
	}

	@Override
	public FunctionPointerExpression functionPointerExpression(
			CIVLSource source, CIVLFunction function) {
		FunctionPointerExpression expression = new CommonFunctionPointerExpression(
				source, function, pointerSymbolicType);

		return expression;
	}

	@Override
	public HereOrRootExpression hereOrRootExpression(CIVLSource source,
			boolean isRoot) {
		CommonHereOrRootExpression result = new CommonHereOrRootExpression(
				source, isRoot);

		result.setExpressionType(this.scopeType);
		return result;
	}

	@Override
	public InitialValueExpression initialValueExpression(CIVLSource source,
			Variable variable) {
		CommonInitialValueExpression result = new CommonInitialValueExpression(
				source, variable);

		// result.setExpressionScope(expressionScope)
		result.setExpressionType(variable.type());
		return result;
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
		IntegerLiteralExpression result = new CommonIntegerLiteralExpression(
				source, value);

		((CommonIntegerLiteralExpression) result)
				.setExpressionType(integerType);
		return result;
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
		QuantifiedExpression result = new CommonQuantifiedExpression(source,
				quantifier, boundVariableName, boundVariableType, restriction,
				expression);

		result.setExpressionScope(join(expression.expressionScope(),
				restriction.expressionScope()));
		((CommonExpression) result).setExpressionType(booleanType);
		return result;
	}

	@Override
	public QuantifiedExpression quantifiedExpression(CIVLSource source,
			Quantifier quantifier, Identifier boundVariableName,
			CIVLType boundVariableType, Expression lower, Expression upper,
			Expression expression) {
		QuantifiedExpression result = new CommonQuantifiedExpression(source,
				quantifier, boundVariableName, boundVariableType, lower, upper,
				expression);

		result.setExpressionScope(join(
				join(expression.expressionScope(), lower.expressionScope()),
				upper.expressionScope()));
		((CommonExpression) result).setExpressionType(booleanType);
		return result;
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
		RealLiteralExpression result = new CommonRealLiteralExpression(source,
				value);

		((CommonRealLiteralExpression) result).setExpressionType(realType);
		return result;
	}

	/**
	 * This expression is only used in an ensures clause of a function contract
	 * to refer to the returned value.
	 * 
	 * @return A result expression.
	 */
	@Override
	public ResultExpression resultExpression(CIVLSource source) {
		return new CommonResultExpression(source);
	}

	@Override
	public ScopeofExpression scopeofExpression(CIVLSource source,
			LHSExpression argument) {
		ScopeofExpression result = new CommonScopeofExpression(source, argument);

		((CommonScopeofExpression) result).setExpressionType(scopeType);
		return result;
	}

	/**
	 * A self expression. Used to referenced the current process.
	 * 
	 * @return A new self expression.
	 */
	@Override
	public SelfExpression selfExpression(CIVLSource source) {
		SelfExpression result = new CommonSelfExpression(source);

		((CommonSelfExpression) result).setExpressionType(processType);
		return result;
	}
	
	@Override
	public ProcnullExpression procnullExpression(CIVLSource source) {
		ProcnullExpression result = new CommonProcnullExpression(source);

		((CommonProcnullExpression) result).setExpressionType(processType);
		return result;
	}

	@Override
	public SizeofExpressionExpression sizeofExpressionExpression(
			CIVLSource source, Expression argument) {
		CommonSizeofExpression result = new CommonSizeofExpression(source,
				argument);

		result.setExpressionScope(argument.expressionScope());
		result.setExpressionType(integerType);
		return result;
	}

	@Override
	public SizeofTypeExpression sizeofTypeExpression(CIVLSource source,
			CIVLType type) {
		CommonSizeofTypeExpression result = new CommonSizeofTypeExpression(
				source, type);
		Variable typeStateVariable = type.getStateVariable();

		// If the type has a state variable, then the scope of the sizeof
		// expression is the scope of the state variable
		if (typeStateVariable != null) {
			result.setExpressionScope(typeStateVariable.scope());
		} else
			// If there is no state variable in the type, then the scope of the
			// sizeof expression is NULL
			result.setExpressionScope(null);
		result.setExpressionType(integerType);
		return result;
	}

	// /**
	// * A string literal expression.
	// *
	// * @param value
	// * The string.
	// * @return The string literal expression.
	// */
	// @Override
	// public StringLiteralExpression stringLiteralExpression(CIVLSource source,
	// String value) {
	// StringLiteralExpression result = new CommonStringLiteralExpression(
	// source, value);
	//
	// ((CommonStringLiteralExpression) result).setExpressionType(stringType);
	// return result;
	// }

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
		SubscriptExpression result = new CommonSubscriptExpression(source,
				array, index);
		CIVLType arrayType = array.getExpressionType();

		result.setExpressionScope(join(array.expressionScope(),
				index.expressionScope()));
		if (arrayType instanceof CIVLArrayType) {
			((CommonSubscriptExpression) result)
					.setExpressionType(((CIVLArrayType) arrayType)
							.elementType());
		} else if (arrayType instanceof CIVLPointerType) {
			((CommonSubscriptExpression) result)
					.setExpressionType(((CIVLPointerType) arrayType).baseType());
		} else {
			throw new RuntimeException(
					"Unable to set expression type for expression: " + result);
		}
		return result;
	}

	@Override
	public SystemFunctionCallExpression systemFunctionCallExpression(
			CallOrSpawnStatement callStatement) {
		return new CommonSystemFunctionCallExpression(null, callStatement);
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
		UnaryExpression result = new CommonUnaryExpression(source, operator,
				operand);

		result.setExpressionScope(operand.expressionScope());
		switch (operator) {
		case NEGATIVE:
		case BIG_O:
			result = new CommonUnaryExpression(source, operator, operand);
			((CommonUnaryExpression) result).setExpressionType(operand
					.getExpressionType());
			break;
		case NOT:
			if (operand.getExpressionType().equals(booleanType)) {
				result = new CommonUnaryExpression(source, operator, operand);
			} else {
				// Expression castOperand = castExpression(source, booleanType,
				// operand);
				result = new CommonUnaryExpression(source, operator,
						this.booleanExpression(operand));
			}
			((CommonUnaryExpression) result).setExpressionType(booleanType);
			break;
		default:
			throw new CIVLInternalException("Unknown unary operator: "
					+ operator, source);

		}
		return result;
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
		VariableExpression result = new CommonVariableExpression(source,
				variable);

		// Don't need to worry about the expression scope of constants.
		if (!variable.isConst()) {
			result.setExpressionScope(variable.scope());
		}
		((CommonVariableExpression) result).setExpressionType(variable.type());
		return result;
	}

	/* *********************************************************************
	 * Fragments and Statements
	 * *********************************************************************
	 */

	/**
	 * An assert statement.
	 * 
	 * @param source
	 *            The source location for this statement.
	 * @param expression
	 *            The expression being asserted.
	 * @return A new assert statement.
	 */
	@Override
	public AssertStatement assertStatement(CIVLSource civlSource,
			Location source, Expression expression) {
		AssertStatement result = new CommonAssertStatement(civlSource, source,
				expression);

		((CommonExpression) result.guard()).setExpressionType(booleanType);
		result.setStatementScope(expression.expressionScope());
		return result;
	}

	/**
	 * An assert statement.
	 * 
	 * @param source
	 *            The source location for this statement.
	 * @param expression
	 *            The expression being asserted.
	 * @return A new assert statement.
	 */
	@Override
	public AssertStatement assertStatement(CIVLSource civlSource,
			Location source, Expression expression,
			ArrayList<Expression> arguments) {
		AssertStatement result = new CommonAssertStatement(civlSource, source,
				expression, arguments);
		Scope scope = expression.expressionScope();

		((CommonExpression) result.guard()).setExpressionType(booleanType);
		for (Expression arg : arguments) {
			scope = join(scope, arg.expressionScope());
		}
		result.setStatementScope(scope);
		return result;
	}

	@Override
	public AssignStatement assignStatement(CIVLSource civlSource,
			Location source, LHSExpression lhs, Expression rhs,
			boolean isInitialization) {
		AssignStatement result = new CommonAssignStatement(civlSource, source,
				lhs, rhs);

		result.setInitialization(isInitialization);
		result.setStatementScope(join(lhs.expressionScope(),
				rhs.expressionScope()));
		((CommonExpression) result.guard()).setExpressionType(booleanType);
		return result;
	}

	/**
	 * An assume statement.
	 * 
	 * @param source
	 *            The source location for this statement.
	 * @param expression
	 *            The expression being added to the path condition.
	 * @return A new assume statement.
	 */
	@Override
	public Fragment assumeFragment(CIVLSource civlSource, Location source,
			Expression expression) {
		AssumeStatement result = new CommonAssumeStatement(civlSource, source,
				expression);

		result.setStatementScope(expression.expressionScope());
		((CommonExpression) result.guard()).setExpressionType(booleanType);
		return new CommonFragment(result);
	}

	// @Override
	// public void enterAtomicBlock(boolean deterministic) {
	// this.atomicBlocks.push(deterministic ? 1 : 0);
	// }
	//
	// @Override
	// public void leaveAtomicBlock(boolean deterministic) {
	// this.atomicBlocks.pop();
	// }

	// @Override
	// public boolean inAtomicBlock() {
	// return !this.atomicBlocks.isEmpty();
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
					start, true);
			leaveAtomic = new CommonAtomBranchStatement(end.getSource(), end,
					false);
		} else {
			enterAtomic = new CommonAtomicLockAssignStatement(
					start.getSource(), start, true,
					this.atomicLockVariableExpression,
					this.selfExpression(systemSource));
			leaveAtomic = new CommonAtomicLockAssignStatement(end.getSource(),
					end, false, this.atomicLockVariableExpression,
					new CommonUndefinedProcessExpression(systemSource));
		}
		startFragment = new CommonFragment(enterAtomic);
		endFragment = new CommonFragment(leaveAtomic);
		start.setEnterAtomic(deterministic);
		for (Statement statement : fragment.startLocation().outgoing()) {
			if (startGuard == null)
				startGuard = statement.guard();
			else {
				startGuard = this.binaryExpression(startGuard.getSource(),
						BINARY_OPERATOR.OR, startGuard, statement.guard());
			}
		}
		if (startGuard != null)
			enterAtomic.setGuard(startGuard);
		end.setLeaveAtomic(deterministic);
		result = startFragment.combineWith(fragment);
		result = result.combineWith(endFragment);
		return result;
	}

	/**
	 * A function call.
	 * 
	 * @param source
	 *            The source location for this call statement.
	 * @param function
	 *            The function.
	 * @param arguments
	 *            The arguments to the function.
	 * @return A new call statement.
	 */
	@Override
	public CallOrSpawnStatement callOrSpawnStatement(CIVLSource civlSource,
			Location source, boolean isCall, List<Expression> arguments,
			Expression guard) {
		CallOrSpawnStatement result = new CommonCallStatement(civlSource,
				source, isCall, null, null, arguments);
		Scope statementScope = null;

		((CommonExpression) result.guard()).setExpressionType(booleanType);
		for (Expression arg : arguments) {
			statementScope = join(statementScope, arg.expressionScope());
		}
		result.setStatementScope(statementScope);
		if (guard != null)
			result.setGuard(guard);
		return result;
	}

	@Override
	public CallOrSpawnStatement callOrSpawnStatement(CIVLSource civlSource,
			Location source, boolean isCall, Expression function,
			List<Expression> arguments, Expression guard) {
		CallOrSpawnStatement result = new CommonCallStatement(civlSource,
				source, isCall, null, function, arguments);
		Scope statementScope = null;

		((CommonExpression) result.guard()).setExpressionType(booleanType);
		for (Expression arg : arguments) {
			statementScope = join(statementScope, arg.expressionScope());
		}
		result.setStatementScope(statementScope);
		if (guard != null)
			result.setGuard(guard);
		return result;
	}

	@Override
	public ChooseStatement chooseStatement(CIVLSource civlSource,
			Location source, LHSExpression lhs, Expression argument) {
		ChooseStatement result;

		if (lhs == null) {
			throw new CIVLInternalException(
					"Side-effect remover failed to translate away function calls as expressions",
					civlSource);
		}
		result = new CommonChooseStatement(civlSource, source, lhs, argument,
				chooseID++);
		result.setStatementScope(join(lhs.expressionScope(),
				argument.expressionScope()));
		((CommonExpression) result.guard()).setExpressionType(booleanType);
		return result;
	}

	@Override
	public NoopStatement gotoBranchStatement(CIVLSource civlSource,
			Location source, String label) {
		NoopStatement result = new CommonGotoBranchStatement(civlSource,
				source, label);

		return result;
	}

	@Override
	public NoopStatement ifElseBranchStatement(CIVLSource civlSource,
			Location source, Expression guard, boolean isTrue) {
		NoopStatement result = new CommonIfElseBranchStatement(civlSource,
				source, isTrue);

		((CommonExpression) result.guard()).setExpressionType(booleanType);
		if (guard != null) {
			result.setGuard(guard);
			result.setStatementScope(guard.expressionScope());
		}
		return result;
	}

	@Override
	public Fragment joinFragment(CIVLSource civlSource, Location source,
			Expression process) {
		WaitStatement result = new CommonWaitStatement(civlSource, source,
				process);
		WaitGuardExpression guard = new CommonWaitGuardExpression(civlSource,
				process, this.booleanType);

		result.setGuard(guard);
		result.setStatementScope(process.expressionScope());
		return new CommonFragment(result);
	}

	@Override
	public NoopStatement loopBranchStatement(CIVLSource civlSource,
			Location source, Expression guard, boolean isTrue) {
		NoopStatement result = new CommonLoopBranchStatement(civlSource,
				source, isTrue);

		((CommonExpression) result.guard()).setExpressionType(booleanType);
		if (guard != null) {
			result.setGuard(guard);
			result.setStatementScope(guard.expressionScope());
		}
		return result;
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
		MallocStatement result = new CommonMallocStatement(civlSource, source,
				mallocId, scopeExpression, staticElementType,
				dynamicElementType, dynamicObjectType, sizeExpression,
				undefinedObject, lhs);

		if (guard != null)
			result.setGuard(guard);
		return result;
	}

	@Override
	public NoopStatement noopStatement(CIVLSource civlSource, Location source) {
		NoopStatement result = new CommonNoopStatement(civlSource, source);

		((CommonExpression) result.guard()).setExpressionType(booleanType);
		return result;
	}

	/**
	 * A noop statement.
	 * 
	 * @param source
	 *            The source location for this noop statement.
	 * @return A new noop statement.
	 */
	@Override
	public NoopStatement noopStatement(CIVLSource civlSource, Location source,
			Expression guard) {
		NoopStatement result = new CommonNoopStatement(civlSource, source);

		((CommonExpression) result.guard()).setExpressionType(booleanType);
		if (guard != null) {
			result.setGuard(guard);
			result.setStatementScope(guard.expressionScope());
		}
		return result;
	}

	@Override
	public NoopStatement switchBranchStatement(CIVLSource civlSource,
			Location source, Expression guard, Expression label) {
		NoopStatement result = new CommonSwitchBranchStatement(civlSource,
				source, label);

		((CommonExpression) result.guard()).setExpressionType(booleanType);
		if (guard != null) {
			result.setGuard(guard);
			result.setStatementScope(guard.expressionScope());
		}
		return result;
	}

	@Override
	public NoopStatement switchBranchStatement(CIVLSource civlSource,
			Location source, Expression guard) {
		NoopStatement result = new CommonSwitchBranchStatement(civlSource,
				source);

		((CommonExpression) result.guard()).setExpressionType(booleanType);
		if (guard != null)
			result.setGuard(guard);
		return result;
	}

	@Override
	public Fragment returnFragment(CIVLSource civlSource, Location source,
			Expression expression, CIVLFunction function) {
		ReturnStatement result = new CommonReturnStatement(civlSource, source,
				expression, function);

		if (expression != null) {
			result.setStatementScope(expression.expressionScope());
		}
		((CommonExpression) result.guard()).setExpressionType(booleanType);
		return new CommonFragment(result);
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
	public CIVLSource sourceOfToken(CToken token) {
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
		Expression condition = expression.getCondition();
		Location startLocation = statement.source();
		Expression ifGuard, elseGuard;
		Statement ifBranch, elseBranch;
		Expression ifValue = expression.getTrueBranch(), elseValue = expression
				.getFalseBranch();
		Fragment result = new CommonFragment();
		StatementSet lastStatement = new StatementSet();

		ifGuard = booleanExpression(condition);
		elseGuard = unaryExpression(condition.getSource(), UNARY_OPERATOR.NOT,
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
					condition.getSource(), startLocation, ifGuard, true));
			ifLocation = location(ifValue.getSource(), scope);
			ifBranch = statement.replaceWith(expression, ifValue);
			ifBranch.setGuard(guard);
			ifBranch.setSource(ifLocation);
			ifFragment = ifFragment.combineWith(new CommonFragment(ifBranch));
			elseFragment = new CommonFragment(ifElseBranchStatement(
					condition.getSource(), startLocation, elseGuard, false));
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
			elseBranch = statement.replaceWith(expression, elseValue);
			ifBranch.setGuard(ifGuard);
			elseBranch.setGuard(elseGuard);
			lastStatement.add(ifBranch);
			lastStatement.add(elseBranch);
			result.setStartLocation(startLocation);
			result.setLastStatement(lastStatement);
		}
		startLocation.removeOutgoing(statement);
		return result;

	}

	@Override
	public Fragment conditionalExpressionToIf(Expression guard,
			VariableExpression variable, ConditionalExpression expression) {
		Expression condition = expression.getCondition();
		Location startLocation = location(condition.getSource(), variable
				.variable().scope());
		Expression ifGuard, elseGuard;
		Statement ifAssign, elseAssign;
		Expression ifValue = expression.getTrueBranch(), elseValue = expression
				.getFalseBranch();
		Fragment result = new CommonFragment();
		StatementSet lastStatement = new StatementSet();

		ifGuard = booleanExpression(condition);
		elseGuard = unaryExpression(condition.getSource(), UNARY_OPERATOR.NOT,
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
		lastStatement.add(ifAssign);
		elseAssign = assignStatement(elseValue.getSource(), startLocation,
				variable, elseValue, false);
		elseAssign.setGuard(elseGuard);
		lastStatement.add(elseAssign);
		result.setStartLocation(startLocation);
		result.setLastStatement(lastStatement);
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
			Expression expression, ExpressionNode expressionNode) {
		Fragment beforeConditionFragment = new CommonFragment();

		while (hasConditionalExpressions()) {
			ConditionalExpression conditionalExpression = pollConditionaExpression();
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
			beforeConditionFragment = this.atomicFragment(false,
					beforeConditionFragment, this.location(
							this.sourceOfBeginning(expressionNode), scope),
					this.location(this.sourceOfEnd(expressionNode), scope));
		}
		return new Pair<Fragment, Expression>(beforeConditionFragment,
				expression);
	}

	@Override
	public Fragment refineConditionalExpressionOfStatement(Statement statement,
			Location oldLocation) {
		Fragment result = new CommonFragment();
		CIVLSource statementSource = statement.getSource();
		Scope scope = statement.source().scope();

		if (sizeofTopConditionalExpressionQueue() == 1)
			return this.conditionalExpressionToIf(
					this.pollConditionaExpression(), statement);
		while (hasConditionalExpressions()) {
			ConditionalExpression conditionalExpression = pollConditionaExpression();
			VariableExpression variable = tempVariable(
					TempVariableKind.CONDITIONAL, scope,
					conditionalExpression.getSource(),
					conditionalExpression.getExpressionType());
			Fragment ifElse = conditionalExpressionToIf(statement.guard(),
					variable, conditionalExpression);

			statement.replaceWith(conditionalExpression, variable);
			result = result.combineWith(ifElse);
		}
		// make the if-else statements atomic
		result = this.atomicFragment(false, result,
				this.location(statementSource, scope),
				this.location(statementSource, scope));
		result = result.combineWith(new CommonFragment(statement));
		return result;
	}

	@Override
	public ConditionalExpression pollConditionaExpression() {
		return conditionalExpressions.peek().pollFirst();
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
	public AssignStatement assignAtomicLockVariable(Integer pid, Location target) {
		// create a new location to avoid breaking the original program graph
		// and this assign statement is unreachable from the original program
		// graph
		AssignStatement assignStatement = this.assignStatement(
				this.systemSource,
				this.location(this.systemSource, target.scope()),
				this.atomicLockVariableExpression,
				this.selfExpression(this.systemSource), false);

		assignStatement.setTarget(target);
		return assignStatement;
	}

	@Override
	public VariableExpression atomicLockVariableExpression() {
		return this.atomicLockVariableExpression;
	}

	@Override
	public void createAtomicLockVariable(Scope scope) {
		// Since the atomic lock variable is not declared explicitly in the CIVL
		// model specification, the system source will be used here.
		Variable variable = this.variable(this.systemSource, processType,
				this.identifier(this.systemSource, ATOMIC_LOCK_VARIABLE), 0);

		this.atomicLockVariableExpression = this.variableExpression(
				this.systemSource, variable);
		scope.addVariable(variable);
	}

	/* *********************************************************************
	 * Other helper methods
	 * *********************************************************************
	 */

	@Override
	public void setImpactScopeOfLocation(Location location) {
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
	public StructOrUnionField structField(Identifier name, CIVLType type) {
		return new CommonStructField(name, type);
	}

	@Override
	public SymbolicExpression undefinedProcessValue() {
		return this.undefinedProcessValue;
	}

	@Override
	public SymbolicExpression nullProcessValue() {
		return this.nullProcessValue;
	}

	@Override
	public void completeBundleType(CIVLBundleType bundleType,
			List<CIVLType> eleTypes, Collection<SymbolicType> elementTypes) {
		LinkedList<SymbolicType> arrayTypes = new LinkedList<SymbolicType>();
		SymbolicUnionType dynamicType;

		for (SymbolicType type : elementTypes)
			arrayTypes.add(universe.arrayType(type));
		dynamicType = universe.unionType(universe.stringObject("$bundle"),
				arrayTypes);
		dynamicType = (SymbolicUnionType) universe.canonic(dynamicType);
		bundleType.complete(eleTypes, elementTypes, dynamicType);
		this.bundleType = bundleType;
		this.bundleSymbolicType = dynamicType;
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
				containingScope, continuity, this);
	}

	@Override
	public CIVLFunction function(CIVLSource source, Identifier name,
			List<Variable> parameters, CIVLType returnType,
			Scope containingScope, Location startLocation) {
		for (Variable v : parameters) {
			if (v.type() instanceof CIVLArrayType) {
				throw new CIVLInternalException("Parameter of array type.", v);
			}
		}
		return new CommonFunction(source, name, parameters, returnType,
				containingScope, startLocation, this);
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
	public Model model(CIVLSource civlSource, CIVLFunction system) {
		return new CommonModel(civlSource, this, system);
	}

	@Override
	public Scope scope(CIVLSource source, Scope parent,
			Set<Variable> variables, CIVLFunction function) {
		Scope newScope = new CommonScope(source, parent, variables, scopeID++);
		int newVid;
		Variable heapVariable;

		if (newScope.id() == 0)
			this.createAtomicLockVariable(newScope);
		newVid = newScope.numVariables();
		heapVariable = this.variable(source, modelBuilder.heapType,
				this.identifier(source, HEAP_VAR), newVid);
		newScope.addVariable(heapVariable);
		if (parent != null) {
			parent.addChild(newScope);
		}
		newScope.setFunction(function);
		// this.currentScope = newScope;
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
		if (libraryName.endsWith("-common")) {
			libraryName = libraryName.substring(0, libraryName.length() - 7);
		}
		return new CommonSystemFunction(source, name, parameters, returnType,
				containingScope, (Location) null, this, libraryName);
	}

	@Override
	public CIVLSource systemSource() {
		return systemSource;
	}

	@Override
	public Variable variable(CIVLSource source, CIVLType type, Identifier name,
			int vid) {
		return new CommonVariable(source, type, name, vid);
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
			result = universe.canonic(universe.tuple(processSymbolicType,
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
	public SymbolicExpression isProcessDefined(CIVLSource source,
			SymbolicExpression processValue) {
		int pid = extractIntField(source, processValue, zeroObj);

		if (pid == -1)
			return universe.falseExpression();
		return universe.trueExpression();
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
			result = universe.canonic(universe.tuple(scopeSymbolicType,
					new Singleton<SymbolicExpression>(universe.integer(sid))));
			scopeValues.set(sid, result);
		}
		return result;
	}

	@Override
	public SymbolicExpression undefinedScopeValue() {
		return this.undefinedScopeValue;
	}
	
	@Override
	public SymbolicExpression nullScopeValue() {
		return this.nullScopeValue;
	}

	@Override
	public SymbolicExpression isScopeDefined(CIVLSource source,
			SymbolicExpression scopeValue) {
		int scopeId = extractIntField(source, scopeValue, zeroObj);

		if (scopeId == -1)
			return universe.falseExpression();
		return universe.trueExpression();
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

	/**
	 * Compute the dynamic heap type, based on the list of malloc statements
	 * encountered in the model.
	 * 
	 * @param mallocStatements
	 *            The list of malloc statements in the model.
	 * @return The symbolic heap type.
	 */
	private SymbolicTupleType computeDynamicHeapType(
			Iterable<MallocStatement> mallocStatements) {
		LinkedList<SymbolicType> fieldTypes = new LinkedList<SymbolicType>();
		SymbolicTupleType result;

		for (MallocStatement statement : mallocStatements) {
			SymbolicType fieldType = universe.arrayType(statement
					.getDynamicObjectType());

			fieldTypes.add(fieldType);
		}
		result = universe.tupleType(universe.stringObject("$heap"), fieldTypes);
		result = (SymbolicTupleType) universe.canonic(result);
		return result;
	}

	/**
	 * Compute the symbolic initial value of a specified heap type.
	 * 
	 * @param heapDynamicType
	 *            The heap type to use.
	 * @return The initial value of the given help type.
	 */
	private SymbolicExpression computeInitialHeapValue(
			SymbolicTupleType heapDynamicType) {
		LinkedList<SymbolicExpression> fields = new LinkedList<SymbolicExpression>();
		SymbolicExpression result;

		for (SymbolicType fieldType : heapDynamicType.sequence()) {
			SymbolicArrayType arrayType = (SymbolicArrayType) fieldType;
			SymbolicType objectType = arrayType.elementType();
			SymbolicExpression emptyArray = universe.emptyArray(objectType);

			fields.add(emptyArray);
		}
		result = universe.tuple(heapDynamicType, fields);
		result = universe.canonic(result);
		return result;
	}

	/**
	 * Gets a Java conrete int from a symbolic expression or throws exception.
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
	protected Scope join(Scope s0, Scope s1) {
		List<Scope> s0Ancestors = new ArrayList<Scope>();
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
	 * Calculate the join scope (the most local common scope) of a list of
	 * expressions.
	 * 
	 * @param expressions
	 *            The list of expressions whose join scope is to be computed.
	 * @return The join scope of the list of expressions.
	 */
	protected Scope joinScope(List<Expression> expressions) {
		Scope scope = null;

		for (Expression expression : expressions) {
			scope = join(scope, expression.expressionScope());
		}
		return scope;
	}

	/**
	 * Calculate the join scope (the most local common scope) of an array of
	 * expressions.
	 * 
	 * @param expressions
	 *            The array of expressions whose join scope is to be computed.
	 * @return The join scope of the array of expressions.
	 */
	protected Scope joinScope(Expression[] expressions) {
		Scope scope = null;

		for (Expression expression : expressions) {
			scope = join(scope, expression.expressionScope());
		}
		return scope;
	}

	/**
	 * Create an instance of a CIVL primitive type, including void, integer,
	 * boolean, real, char, scope, process, and dynamic types.
	 * 
	 * @param kind
	 *            The kind of the primitive type. See also
	 *            {@link PrimitiveTypeKind}.
	 * @param dynamicType
	 *            The corresponding SARL symbolic type of the CIVL primitive
	 *            type.
	 * @return The CIVL primitive type of the given kind.
	 */
	private CIVLPrimitiveType primitiveType(PrimitiveTypeKind kind,
			SymbolicType dynamicType) {
		CIVLPrimitiveType result;
		NumericExpression size = null;
		BooleanExpression fact = null;

		if (dynamicType != null)
			dynamicType = (SymbolicType) universe.canonic(dynamicType);
		if (kind != PrimitiveTypeKind.VOID)
			size = sizeofExpression(kind);
		if (size == null)
			fact = universe.trueExpression();
		else
			fact = universe.lessThan(universe.zeroInt(), size);
		fact = (BooleanExpression) universe.canonic(fact);
		result = new CommonPrimitiveType(kind, dynamicType, size, fact);
		return result;
	}

	/**
	 * Create a new numeric expression for a sizeof expression of a certain
	 * primitive type.
	 * 
	 * @param kind
	 *            The kind of the primitive type of the sizeof expression.
	 * @return The numeric expression of the sizeof expression.
	 */
	private NumericExpression sizeofExpression(PrimitiveTypeKind kind) {
		NumericExpression result = (NumericExpression) universe
				.symbolicConstant(universe.stringObject("SIZEOF_" + kind),
						universe.integerType());

		result = (NumericExpression) universe.canonic(result);
		return result;
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
		((CommonVariableExpression) result).setExpressionType(variable.type());
		return result;
	}

	/**
	 * generate undefined value of a certain type
	 * 
	 * @param type
	 * @return
	 */
	private SymbolicExpression undefinedValue(SymbolicType type) {
		SymbolicExpression result = universe.symbolicConstant(
				universe.stringObject("UNDEFINED"), type);

		result = universe.canonic(result);
		return result;
	}

	@Override
	public ArrayLiteralExpression arrayLiteralExpression(CIVLSource source,
			CIVLType arrayType, ArrayList<Expression> elements) {
		ArrayLiteralExpression arrayLiteral = new CommonArrayLiteralExpression(
				source, arrayType, elements);
		Scope expressionScope = null;

		if (elements != null) {
			expressionScope = joinScope(elements);
			// for (Expression element : elements) {
			// expressionScope = join(expressionScope,
			// element.expressionScope());
			// }
		}
		if (expressionScope != null)
			arrayLiteral.setExpressionScope(expressionScope);
		return arrayLiteral;
	}

	@Override
	public StructOrUnionLiteralExpression structOrUnionLiteralExpression(
			CIVLSource source, CIVLType structType, ArrayList<Expression> fields) {
		StructOrUnionLiteralExpression structLiteral = new CommonStructOrUnionLiteralExpression(
				source, structType, fields);
		Scope expressionScope = null;

		if (fields != null) {
			// for (Expression field : fields) {
			// expressionScope = join(expressionScope, field.expressionScope());
			// }
			expressionScope = joinScope(fields);
		}
		if (expressionScope != null)
			structLiteral.setExpressionScope(expressionScope);
		return structLiteral;
	}

	@Override
	public CharLiteralExpression charLiteralExpression(CIVLSource sourceOf,
			char value) {
		return new CommonCharLiteralExpression(sourceOf, this.charType, value);
	}

	@Override
	public Variable newAnonymousVariableForArrayLiteral(CIVLSource sourceOf,
			Scope scope, CIVLArrayType type) {
		String name = ANONYMOUS_VARIABLE_PREFIX + this.anonymousVariableId++;
		Variable variable = this.variable(sourceOf, type,
				this.identifier(null, name), scope.numVariables());

		variable.setConst(true);
		scope.addVariable(variable);
		return variable;
	}

	@Override
	public Scope currentScope() {
		return this.currentScope;
	}

	@Override
	public Fragment anonFragment() {
		return this.anonFragment;
	}

	@Override
	public void resetAnonFragment() {
		this.anonFragment = new CommonFragment();
	}

	@Override
	public void addAnonStatement(Statement statement) {
		this.anonFragment.addNewStatement(statement);
	}

	@Override
	public void setCurrentScope(Scope scope) {
		this.currentScope = scope;
	}

	@Override
	public CIVLHeapType heapType() {
		return this.heapType;
	}

	@Override
	public SymbolicTupleType heapSymbolicType() {
		return this.heapSymbolicType;
	}

	@Override
	public CIVLBundleType bundleType() {
		return this.bundleType;
	}

	@Override
	public SymbolicUnionType bundleSymbolicType() {
		return this.bundleSymbolicType;
	}

	@Override
	public Expression systemGuardExpression(CallOrSpawnStatement call) {
		SystemGuardExpression systemGuard = new CommonSystemGuardExpression(
				call.getSource(),
				((SystemFunction) call.function()).getLibrary(), call
						.function().name().name(), call.arguments(),
				this.booleanType);

		if (this.isTrue(call.guard()))
			return systemGuard;
		return this.binaryExpression(call.guard().getSource(),
				BINARY_OPERATOR.AND, call.guard(), systemGuard);
	}

	@Override
	public Expression functionGuardExpression(CIVLSource source,
			Expression function, List<Expression> arguments) {
		FunctionGuardExpression functionGuard = new CommonFunctionGuardExpression(
				source, function, arguments, this.booleanType);

		return functionGuard;
	}

	@Override
	public Model model() {
		return this.modelBuilder.getModel();
	}

}
