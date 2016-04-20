package edu.udel.cis.vsl.civl.model.common;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
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
import edu.udel.cis.vsl.abc.program.IF.Program;
import edu.udel.cis.vsl.abc.token.IF.CToken;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.TokenFactory;
import edu.udel.cis.vsl.civl.model.IF.AbstractFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLException;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
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
import edu.udel.cis.vsl.civl.model.IF.expression.MemoryUnitExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ProcnullExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.QuantifiedExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.QuantifiedExpression.Quantifier;
import edu.udel.cis.vsl.civl.model.IF.expression.RealLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.RecDomainLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.RegularRangeExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ResultExpression;
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
import edu.udel.cis.vsl.civl.model.IF.expression.reference.ArraySliceReference;
import edu.udel.cis.vsl.civl.model.IF.expression.reference.ArraySliceReference.ArraySliceKind;
import edu.udel.cis.vsl.civl.model.IF.expression.reference.MemoryUnitReference;
import edu.udel.cis.vsl.civl.model.IF.expression.reference.SelfReference;
import edu.udel.cis.vsl.civl.model.IF.expression.reference.StructOrUnionFieldReference;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.AssignStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.CivlParForEnterStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.MallocStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.NextInDomainStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.NoopStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.statement.StatementList;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLBundleType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLCompleteArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLCompleteDomainType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLDomainType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLEnumType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLFunctionType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLHeapType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPointerType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPrimitiveType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPrimitiveType.PrimitiveTypeKind;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLRegularRangeType;
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
import edu.udel.cis.vsl.civl.model.common.expression.CommonDomainGuardExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonDotExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonDynamicTypeOfExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonFunctionGuardExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonFunctionIdentifierExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonHereOrRootExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonInitialValueExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonIntegerLiteralExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonMemoryUnitExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonProcnullExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonQuantifiedExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonRealLiteralExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonRecDomainLiteralExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonRegularRangeExpression;
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
import edu.udel.cis.vsl.civl.model.common.expression.reference.CommonArraySliceReference;
import edu.udel.cis.vsl.civl.model.common.expression.reference.CommonSelfReference;
import edu.udel.cis.vsl.civl.model.common.expression.reference.CommonStructOrUnionFieldReference;
import edu.udel.cis.vsl.civl.model.common.location.CommonLocation;
import edu.udel.cis.vsl.civl.model.common.statement.CommonAssertStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonAssignStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonAssumeStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonAtomBranchStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonAtomicLockAssignStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonCallStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonCivlForEnterStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonCivlParForEnterStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonGotoBranchStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonIfElseBranchStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonLoopBranchStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonMallocStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonNoopStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonReturnStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonStatementList;
import edu.udel.cis.vsl.civl.model.common.statement.CommonSwitchBranchStatement;
import edu.udel.cis.vsl.civl.model.common.statement.StatementSet;
import edu.udel.cis.vsl.civl.model.common.type.CommonArrayType;
import edu.udel.cis.vsl.civl.model.common.type.CommonBundleType;
import edu.udel.cis.vsl.civl.model.common.type.CommonCompleteArrayType;
import edu.udel.cis.vsl.civl.model.common.type.CommonCompleteDomainType;
import edu.udel.cis.vsl.civl.model.common.type.CommonDomainType;
import edu.udel.cis.vsl.civl.model.common.type.CommonEnumType;
import edu.udel.cis.vsl.civl.model.common.type.CommonFunctionType;
import edu.udel.cis.vsl.civl.model.common.type.CommonHeapType;
import edu.udel.cis.vsl.civl.model.common.type.CommonPointerType;
import edu.udel.cis.vsl.civl.model.common.type.CommonPrimitiveType;
import edu.udel.cis.vsl.civl.model.common.type.CommonRegularRangeType;
import edu.udel.cis.vsl.civl.model.common.type.CommonStructOrUnionField;
import edu.udel.cis.vsl.civl.model.common.type.CommonStructOrUnionType;
import edu.udel.cis.vsl.civl.model.common.variable.CommonVariable;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.civl.util.IF.Singleton;
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

	private static final String ANONYMOUS_VARIABLE_PREFIX = "_anon_";

	private static final String DOM_SIZE_PREFIX = "_dom_size";

	private static final String PAR_PROC_PREFIX = "_par_procs";

	/* ************************** Instance Fields ************************** */

	private int domSizeVariableId = 0;

	private int parProcsVariableId = 0;

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

	private VariableExpression civlFilesystemVariableExpression;

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
	private List<SymbolicExpression> processValues = new ArrayList<SymbolicExpression>();

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

	private CIVLRegularRangeType rangeType = null;

	private CIVLDomainType domainType = null;

	private FunctionIdentifierExpression waitallFuncPointer;

	private Map<String, CIVLType> systemTypes = new HashMap<>();

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
		this.rangeType = new CommonRegularRangeType(new CommonIdentifier(
				this.systemSource, (StringObject) universe.canonic(universe
						.stringObject("$regular_range"))), universe,
				integerType);
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
		Scope lowestScope = getLower(arguments);

		return new CommonAbstractFunctionCallExpression(source,
				expressionScope, lowestScope, function, arguments);
	}

	@Override
	public AddressOfExpression addressOfExpression(CIVLSource source,
			LHSExpression operand) {
		return new CommonAddressOfExpression(source, this.pointerType(operand
				.getExpressionType()), operand);
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
					lowestScope, booleanType, operator, left, right);
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
					resultType = integerType();
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
				throw new ModelFactoryException();
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
		return new CommonBooleanLiteralExpression(source, booleanType, value);
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

		return new CommonConditionalExpression(source, joinScope(Arrays.asList(
				condition, trueBranch, falseBranch)), getLower(Arrays.asList(
				condition, trueBranch, falseBranch)),
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
				getLower(arguments), function, partials, arguments);
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
		return new CommonDynamicTypeOfExpression(source, dynamicType, type);
	}

	@Override
	public FunctionIdentifierExpression functionPointerExpression(
			CIVLSource source, CIVLFunction function) {
		FunctionIdentifierExpression expression = new CommonFunctionIdentifierExpression(
				source, function, pointerSymbolicType);

		return expression;
	}

	@Override
	public HereOrRootExpression hereOrRootExpression(CIVLSource source,
			boolean isRoot) {
		return new CommonHereOrRootExpression(source, this.scopeType, isRoot,
				isRoot ? this.scopeValue(this.systemScope.id()) : null);
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
		return new CommonIntegerLiteralExpression(source, this.integerType,
				value);
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
				booleanType, quantifier, boundVariableName, boundVariableType,
				restriction, expression);
	}

	@Override
	public QuantifiedExpression quantifiedExpression(CIVLSource source,
			Quantifier quantifier, Identifier boundVariableName,
			CIVLType boundVariableType, Expression lower, Expression upper,
			Expression expression) {
		return new CommonQuantifiedExpression(source, join(
				join(expression.expressionScope(), lower.expressionScope()),
				upper.expressionScope()), this.booleanType, quantifier,
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
		return new CommonRealLiteralExpression(source, this.realType, value);
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
		return new CommonScopeofExpression(source, this.scopeType, argument);
	}

	/**
	 * A self expression. Used to referenced the current process.
	 * 
	 * @return A new self expression.
	 */
	@Override
	public SelfExpression selfExpression(CIVLSource source) {
		return new CommonSelfExpression(source, this.processType);
	}

	@Override
	public ProcnullExpression procnullExpression(CIVLSource source) {
		return new CommonProcnullExpression(source, processType,
				this.nullProcessValue);
	}

	@Override
	public SizeofExpression sizeofExpressionExpression(CIVLSource source,
			Expression argument) {
		return new CommonSizeofExpression(source, this.integerType, argument);
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
				integerType, type);
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
			return new CommonUnaryExpression(source, booleanType, operator,
					operand);
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
		return new CommonFragment(new CommonAssumeStatement(civlSource, source,
				this.trueExpression(civlSource), expression));
	}

	@Override
	public Fragment assertFragment(CIVLSource civlSource, Location source,
			Expression condition, Expression[] explanation) {
		Scope statementScope = condition.expressionScope();
		Scope lowestScope = condition.lowestScope();
		Scope lowestScopeExplanation = getLower(explanation);

		if (explanation != null)
			for (Expression arg : explanation) {
				statementScope = join(statementScope, arg.expressionScope());
			}
		return new CommonFragment(
				new CommonAssertStatement(civlSource, statementScope, getLower(
						lowestScope, lowestScopeExplanation), source, this
						.trueExpression(civlSource), condition, explanation));
	}

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
			leaveAtomic = new CommonAtomicLockAssignStatement(end.getSource(),
					this.systemScope, this.systemScope, end,
					this.trueExpression(end.getSource()), false,
					this.atomicLockVariableExpression,
					new CommonUndefinedProcessExpression(systemSource,
							this.processType, this.undefinedProcessValue));
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
		return this.callOrSpawnStatement(civlSource, source, isCall, null,
				arguments, guard);
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
				getLower(arguments), source, guard != null ? guard
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
				getLower(Arrays.asList(lhs, scopeExpression, sizeExpression)),
				source,
				guard != null ? guard : this.trueExpression(civlSource),
				mallocId, scopeExpression, staticElementType,
				dynamicElementType, dynamicObjectType, sizeExpression,
				undefinedObject, lhs);
	}

	@Override
	public NoopStatement noopStatement(CIVLSource civlSource, Location source) {
		return new CommonNoopStatement(civlSource, source,
				this.trueExpression(civlSource));
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
		return new CommonNoopStatement(civlSource, source,
				guard != null ? guard : this.trueExpression(civlSource));
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
	public StatementList statmentList(Statement stmt) {
		return new CommonStatementList(stmt);
	}

	@Override
	public StatementList statmentList(Statement stmt1, Statement stmt2) {
		return new CommonStatementList(stmt1, stmt2);
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
		Location startLocation = statement.source();
		Expression ifGuard = expression.getCondition(), elseGuard;
		Statement ifBranch, elseBranch;
		Expression ifValue = expression.getTrueBranch(), elseValue = expression
				.getFalseBranch();
		Fragment result = new CommonFragment();
		StatementSet lastStatement = new StatementSet();

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
		Expression ifGuard = expression.getCondition(), elseGuard;
		Location startLocation = location(ifGuard.getSource(), variable
				.variable().scope());
		Statement ifAssign, elseAssign;
		Expression ifValue = expression.getTrueBranch(), elseValue = expression
				.getFalseBranch();
		Fragment result = new CommonFragment();
		StatementSet lastStatement = new StatementSet();

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
			Expression expression, CIVLSource startSource, CIVLSource endSource) {
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
					beforeConditionFragment, this.location(startSource, scope),
					this.location(endSource, scope));
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

		assignStatement.setTargetTemp(target);
		return assignStatement;
	}

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
		Variable variable = this.variable(this.systemSource, processType, this
				.identifier(this.systemSource,
						ModelConfiguration.ATOMIC_LOCK_VARIABLE), scope
				.numVariables());

		this.atomicLockVariableExpression = this.variableExpression(
				this.systemSource, variable);
		scope.addVariable(variable);
	}

	private void createTimeVariables(Scope scope) {
		// Since the atomic lock variable is not declared explicitly in the CIVL
		// model specification, the system source will be used here.
		timeCountVariable = this.variable(this.systemSource, this.integerType,
				this.identifier(this.systemSource,
						ModelConfiguration.TIME_COUNT_VARIABLE), scope
						.numVariables());
		timeCountVariable.setStatic(true);
		scope.addVariable(timeCountVariable);
		if (modelBuilder.timeLibIncluded) {
			brokenTimeVariable = this.variable(this.systemSource,
					this.integerType, this.identifier(systemSource,
							ModelConfiguration.BROKEN_TIME_VARIABLE), scope
							.numVariables());
			scope.addVariable(brokenTimeVariable);
		}
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
		return new CommonStructOrUnionField(name, type);
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
			if (v.type().isArrayType()) {
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

	private Scope getLower(Expression[] expressions) {
		if (expressions == null)
			return null;
		return getLower(Arrays.asList(expressions));
	}

	private Scope getLower(List<Expression> expressions) {
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
		return result;
	}

	@Override
	public SymbolicExpression undefinedValue(SymbolicType type) {
		SymbolicExpression result = universe.symbolicConstant(
				universe.stringObject("UNDEFINED"), type);

		result = universe.canonic(result);
		return result;
	}

	@Override
	public ArrayLiteralExpression arrayLiteralExpression(CIVLSource source,
			CIVLArrayType arrayType, List<Expression> elements) {
		return new CommonArrayLiteralExpression(source, joinScope(elements),
				getLower(elements), arrayType, elements);
	}

	@Override
	public StructOrUnionLiteralExpression structOrUnionLiteralExpression(
			CIVLSource source, CIVLType structType, List<Expression> fields) {
		return new CommonStructOrUnionLiteralExpression(source,
				joinScope(fields), getLower(fields), structType, fields);
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
				call.getSource(), call.statementScope(),
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
	public Fragment nextInDomain(CIVLSource source, Location src,
			Expression dom, List<Variable> variables, Variable counter) {
		NextInDomainStatement statement = new CommonCivlForEnterStatement(
				source, src, this.trueExpression(source), dom, variables,
				counter);

		return new CommonFragment(statement);
	}

	@Override
	public RegularRangeExpression regularRangeExpression(CIVLSource source,
			Expression low, Expression high, Expression step) {
		return new CommonRegularRangeExpression(source,
				joinScope(Arrays.asList(low, high, step)),
				getLower(Arrays.asList(low, high, step)), this.rangeType, low,
				high, step);
	}

	@Override
	public CIVLType rangeType() {
		return this.rangeType;
	}

	@Override
	public CIVLDomainType domainType(CIVLType rangeType) {
		if (this.domainType == null) {
			this.domainType = new CommonDomainType(rangeType);
		}
		return this.domainType;
	}

	@Override
	public RecDomainLiteralExpression recDomainLiteralExpression(
			CIVLSource source, List<Expression> ranges, CIVLType type) {
		return new CommonRecDomainLiteralExpression(source, getLower(ranges),
				ranges, type);
	}

	@Override
	public DomainGuardExpression domainGuard(CIVLSource source,
			List<Variable> vars, Variable counter, Expression domain) {
		return new CommonDomainGuardExpression(source, this.booleanType,
				domain, vars, counter);
	}

	@Override
	public VariableExpression domSizeVariable(CIVLSource source, Scope scope) {
		Variable variable = this.variable(
				source,
				integerType,
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
	public CivlParForEnterStatement civlParForEnterStatement(CIVLSource source,
			Location location, Expression domain, VariableExpression domSize,
			VariableExpression procsVar, Expression parProcs,
			CIVLFunction parProcFunc) {
		return new CommonCivlParForEnterStatement(source, location,
				this.trueExpression(source), domain, domSize, procsVar,
				parProcs, parProcFunc);
	}

	@Override
	public FunctionIdentifierExpression waitallFunctionPointer() {
		if (this.waitallFuncPointer == null) {
			List<Variable> parameters = new ArrayList<>(2);
			CIVLFunction function;

			parameters.add(this.variable(systemSource,
					this.pointerType(this.processType),
					this.identifier(systemSource, "procs"), 1));
			parameters.add(this.variable(systemSource, this.integerType,
					this.identifier(systemSource, "num"), 2));
			function = this.systemFunction(systemSource,
					this.identifier(systemSource, "$waitall"), parameters,
					this.voidType, systemScope, "civlc");
			this.waitallFuncPointer = this.functionPointerExpression(
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
	public void addSystemType(String name, CIVLType type) {
		this.systemTypes.put(name, type);
	}

	@Override
	public CIVLType getSystemType(String name) {
		return systemTypes.get(name);
	}

	@Override
	public CIVLCompleteDomainType completeDomainType(CIVLType rangeType, int dim) {
		return new CommonCompleteDomainType(rangeType, dim);
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
}
