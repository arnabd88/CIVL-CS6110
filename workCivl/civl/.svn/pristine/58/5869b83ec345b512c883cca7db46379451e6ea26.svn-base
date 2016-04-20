package edu.udel.cis.vsl.civl.semantics.common;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.model.IF.AbstractFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLException;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLSyntaxException;
import edu.udel.cis.vsl.civl.model.IF.CIVLTypeFactory;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
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
import edu.udel.cis.vsl.civl.model.IF.expression.DereferenceExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DerivativeCallExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DomainGuardExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DotExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DynamicTypeOfExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression.ExpressionKind;
import edu.udel.cis.vsl.civl.model.IF.expression.FunctionGuardExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.FunctionIdentifierExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.HereOrRootExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.InitialValueExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.IntegerLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ProcnullExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.QuantifiedExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.RealLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.RecDomainLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.RegularRangeExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ScopeofExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SelfExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SizeofExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SizeofTypeExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.StructOrUnionLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SubscriptExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SystemGuardExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
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
import edu.udel.cis.vsl.civl.model.IF.type.CIVLStructOrUnionType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType.TypeKind;
import edu.udel.cis.vsl.civl.model.IF.type.StructOrUnionField;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryLoaderException;
import edu.udel.cis.vsl.civl.semantics.IF.MemoryUnitExpressionEvaluator;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.MemoryUnitFactory;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.civl.util.IF.Singleton;
import edu.udel.cis.vsl.civl.util.IF.Triple;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SARLException;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.ArrayElementReference;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.OffsetReference;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.expr.TupleComponentReference;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicFunctionType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicUnionType;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicSequence;
import edu.udel.cis.vsl.sarl.number.IF.Numbers;

/**
 * An evaluator is used to evaluate expressions.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class CommonEvaluator implements Evaluator {

	private static String ABSTRACT_FUNCTION_PREFIX = "_uf_";
	private static String POINTER_TO_INT_FUNCTION = "_pointer2Int";
	private static String INT_TO_POINTER_FUNCTION = "_int2Pointer";

	/* *************************** Instance Fields ************************* */

	private CIVLConfiguration civlConfig;

	/**
	 * The library evaluator loader. This is used to location and obtain the
	 * appropriate library evaluators when library-defined expressions need to
	 * be evaluated. These are primarily guards of system functions.
	 */
	protected LibraryEvaluatorLoader libLoader;

	/**
	 * An uninterpreted function used to evaluate "BigO" of an expression. It
	 * takes as input one expression of real type and return a real type,
	 * <code>real $O(real x)</code>.
	 */
	private SymbolicExpression bigOFunction;

	/**
	 * TODO: clean up boundVariables, which becomes a "state" of the evaluator
	 * but it is not necessary. Possible solution: creates an evaluator worker<br>
	 * 
	 * LinkedList used to store a stack of bound variables during evaluation of
	 * (possibly nested) quantified expressions. LinkedList is used instead of
	 * Stack because of its more intuitive iteration order.
	 */
	private LinkedList<SymbolicConstant> boundVariables = new LinkedList<>();

	/**
	 * The dynamic heap type. This is the symbolic type of a symbolic expression
	 * which represents the value of an entire heap. It is a tuple in which
	 * there is one component for each <code>malloc</code> statement in a CIVL
	 * model. A component of such a tuple is used to represent all the object
	 * allocated by the corresponding <code>malloc</code> statement. Such a
	 * component has type "array of array of T", where T is the type that occurs
	 * as in an expression of the form <code>(T*)malloc(n*sizeof(T))</code>.
	 */
	private SymbolicTupleType heapType;

	/**
	 * The identity reference expression. A symbolic reference expression can be
	 * viewed as a function which takes a symbolic expression x (of the
	 * appropriate type) and returns a sub-expression of x. The identify
	 * reference, viewed this way, corresponds to the identify function: given x
	 * it returns x.
	 */
	private ReferenceExpression identityReference;

	/**
	 * The unique model factory used to construct the CIVL model elements that
	 * this evaluator will encounter.
	 */
	protected ModelFactory modelFactory;

	/**
	 * The symbolic expression representing "NULL" expression, which is non-null
	 * (as a Java object) but represents the absence of some value. It is used
	 * in CIVL to represent the undefined value: it is the value assigned to
	 * variables before they are initialized. Note that this is the only
	 * symbolic expression that does not have a type.
	 */
	private SymbolicExpression nullExpression;

	/**
	 * The unique real number factory used in the system.
	 */
	private NumberFactory numberFactory = Numbers.REAL_FACTORY;

	/**
	 * The symbolic expression 1 of integer type. (Note that this is distinct
	 * from the 1 of real type.)
	 */
	private NumericExpression one;

	/**
	 * The pointer value is a triple <s,v,r> where s identifies the dynamic
	 * scope, v identifies the variable within that scope, and r identifies a
	 * point within that variable. The type of s is scopeType, which is just a
	 * tuple wrapping a single integer which is the dynamic scope ID number. The
	 * type of v is integer; it is the (static) variable ID number for the
	 * variable in its scope. The type of r is ReferenceExpression from SARL.
	 */
	private SymbolicTupleType pointerType;

	/**
	 * The function pointer value is a pair <s,i> where s identifies the dynamic
	 * scope, i is the function id in the scope. The type of s is scopeType,
	 * which is just a tuple wrapping a single integer which is the dynamic
	 * scope ID number. The type of i is integer. Function pointer type need to
	 * be different from pointer type, because there is analysis particularly
	 * for pointers, like heap object reachability, reachable memory units, etc.
	 */
	private SymbolicTupleType functionPointerType;

	/**
	 * An uninterpreted function used to evaluate "sizeof" on a type. It takes
	 * as input one expression of type dynamicType and returns an integer
	 * expression.
	 */
	private SymbolicExpression sizeofFunction;

	/**
	 * The unique state factory used in the system.
	 */
	private StateFactory stateFactory;

	/**
	 * The unique symbolic universe used in the system.
	 */
	protected SymbolicUniverse universe;

	/**
	 * The symbolic int object of 0.
	 */
	private IntObject zeroObj;

	/**
	 * The symbolic int object of 2.
	 */
	private IntObject twoObj;

	/**
	 * The symbolic numeric expression of 0 of integer type.
	 */
	private NumericExpression zero;

	/**
	 * The symbolic numeric expression of 0 of real type.
	 */
	private NumericExpression zeroR;

	/** The SARL character type. */
	private SymbolicType charType;

	/**
	 * The SARL character 0, i.e., '\0' or '\u0000', used as the
	 * "null character constant" in C.
	 */
	private SymbolicExpression nullCharExpr;

	/**
	 * The symbolic utility for manipulations of symbolic expressions.
	 */
	protected SymbolicUtility symbolicUtil;

	/**
	 * The error logger to report errors.
	 */
	protected CIVLErrorLogger errorLogger;

	/**
	 * The abstract function for bitwise and.
	 */
	private SymbolicConstant bitAndFunc;

	/**
	 * The abstract function for bitwise complement.
	 */
	private SymbolicConstant bitComplementFunc;

	/**
	 * The abstract function for bitwise or.
	 */
	private SymbolicConstant bitOrFunc;

	/**
	 * The abstract function for bitwise xor.
	 */
	private SymbolicConstant bitXorFunc;

	/**
	 * The abstract function for bitwise left shift.
	 */
	private SymbolicConstant shiftLeftFunc;

	/**
	 * The abstract function for bitwise right shift.
	 */
	private SymbolicConstant shiftRightFunc;

	/**
	 * The symbolic numeric expression that has the value of either zero or one.
	 */
	// private NumericExpression zeroOrOne;

	/**
	 * The symbolic analyzer to be used.
	 */
	protected SymbolicAnalyzer symbolicAnalyzer;

	private MemoryUnitExpressionEvaluator memUnitEvaluator;

	private CIVLTypeFactory typeFactory;

	private SymbolicConstant pointer2IntFunc;

	private SymbolicConstant int2PointerFunc;

	/* ***************************** Constructors ************************** */

	/**
	 * Create a new instance of evaluator for evaluating expressions.
	 * 
	 * @param modelFactory
	 *            The model factory of the system.
	 * @param stateFactory
	 *            The state factory of the system.
	 * @param loader
	 *            The loader for library evaluators.
	 * @param symbolicUtil
	 *            The symbolic utility.
	 * @param symbolicAnalyzer
	 *            The symbolic analyzer used in the system.
	 * @param errorLogger
	 *            The error logger for logging errors.
	 */
	public CommonEvaluator(ModelFactory modelFactory,
			StateFactory stateFactory, LibraryEvaluatorLoader loader,
			SymbolicUtility symbolicUtil, SymbolicAnalyzer symbolicAnalyzer,
			MemoryUnitFactory memUnitFactory, CIVLErrorLogger errorLogger,
			CIVLConfiguration config) {
		this.libLoader = loader;
		this.errorLogger = errorLogger;
		this.symbolicUtil = symbolicUtil;
		this.symbolicAnalyzer = symbolicAnalyzer;
		((CommonSymbolicAnalyzer) symbolicAnalyzer).setEvaluator(this);
		this.modelFactory = modelFactory;
		this.typeFactory = modelFactory.typeFactory();
		this.stateFactory = stateFactory;
		this.universe = stateFactory.symbolicUniverse();
		this.memUnitEvaluator = new CommonMemoryUnitEvaluator(symbolicUtil,
				this, memUnitFactory, universe);
		pointerType = typeFactory.pointerSymbolicType();
		functionPointerType = typeFactory.functionPointerSymbolicType();
		heapType = typeFactory.heapSymbolicType();
		zeroObj = (IntObject) universe.canonic(universe.intObject(0));
		// oneObj = (IntObject) universe.canonic(universe.intObject(1));
		twoObj = (IntObject) universe.canonic(universe.intObject(2));
		identityReference = (ReferenceExpression) universe.canonic(universe
				.identityReference());
		zero = (NumericExpression) universe.canonic(universe.integer(0));
		zeroR = (NumericExpression) universe.canonic(universe.zeroReal());
		one = (NumericExpression) universe.canonic(universe.integer(1));
		nullExpression = universe.nullExpression();
		sizeofFunction = symbolicUtil.sizeofFunction();
		bigOFunction = universe.symbolicConstant(
				universe.stringObject("BIG_O"), universe.functionType(
						new Singleton<SymbolicType>(universe.realType()),
						universe.realType()));
		bigOFunction = universe.canonic(bigOFunction);
		charType = universe.characterType();
		nullCharExpr = universe.canonic(universe.character('\u0000'));
		this.bitAndFunc = universe.symbolicConstant(universe
				.stringObject("bitand"), universe.functionType(
				Arrays.asList(universe.integerType(), universe.integerType()),
				universe.integerType()));
		this.bitComplementFunc = universe.symbolicConstant(universe
				.stringObject("bitcomplement"), universe.functionType(
				Arrays.asList(universe.integerType(), universe.integerType()),
				universe.integerType()));
		this.bitOrFunc = universe.symbolicConstant(universe
				.stringObject("bitor"), universe.functionType(
				Arrays.asList(universe.integerType(), universe.integerType()),
				universe.integerType()));
		this.bitXorFunc = universe.symbolicConstant(universe
				.stringObject("bitxor"), universe.functionType(
				Arrays.asList(universe.integerType(), universe.integerType()),
				universe.integerType()));
		this.shiftLeftFunc = universe.symbolicConstant(universe
				.stringObject("shiftleft"), universe.functionType(
				Arrays.asList(universe.integerType(), universe.integerType()),
				universe.integerType()));
		this.shiftRightFunc = universe.symbolicConstant(universe
				.stringObject("shiftright"), universe.functionType(
				Arrays.asList(universe.integerType(), universe.integerType()),
				universe.integerType()));
		pointer2IntFunc = universe.symbolicConstant(universe
				.stringObject(POINTER_TO_INT_FUNCTION), universe.functionType(
				Arrays.asList(this.pointerType), this.universe.integerType()));
		int2PointerFunc = universe.symbolicConstant(universe
				.stringObject(INT_TO_POINTER_FUNCTION), universe.functionType(
				Arrays.asList(this.universe.integerType()), this.pointerType));
		this.civlConfig = config;
		// this.zeroOrOne = (NumericExpression) universe.symbolicConstant(
		// universe.stringObject("ZeroOrOne"), universe.integerType());
	}

	/* ************************** Private Methods ************************** */

	/**
	 * Dereferences a pointer. Logs error when the dereference fails, like when
	 * the pointer is null.
	 * 
	 * @param source
	 *            Source code information for error report.
	 * @param state
	 *            The state where the dereference happens.
	 * @param process
	 *            The process name for error report.
	 * @param pointer
	 *            The pointer to be dereferenced.
	 * @param checkOutput
	 *            Is reading of output variable to be checked?
	 * @param analysisOnly
	 *            Is this called from pointer reachability analysis?
	 * @return A possibly new state and the value of memory space pointed by the
	 *         pointer.
	 * @throws UnsatisfiablePathConditionException
	 */
	Evaluation dereference(CIVLSource source, State state, String process,
			Expression pointerExpression, SymbolicExpression pointer,
			boolean checkOutput, boolean analysisOnly)
			throws UnsatisfiablePathConditionException {
		boolean throwPCException = false;
		SymbolicExpression deref = null;

		if (!pointer.type().equals(this.pointerType)) {
			errorLogger.logSimpleError(source, state, process,
					this.symbolicAnalyzer.stateInformation(state),
					ErrorKind.UNDEFINED_VALUE,
					"attempt to deference an invalid pointer");
			throwPCException = true;
		} else if (pointer.operator() != SymbolicOperator.CONCRETE) {
			errorLogger.logSimpleError(source, state, process,
					this.symbolicAnalyzer.stateInformation(state),
					ErrorKind.UNDEFINED_VALUE,
					"attempt to deference a pointer that is never initialized");
			throwPCException = true;
		} else if (symbolicUtil.isNullPointer(pointer)) {
			// null pointer dereference
			errorLogger.logSimpleError(source, state, process,
					this.symbolicAnalyzer.stateInformation(state),
					ErrorKind.DEREFERENCE,
					"attempt to deference a null pointer");
			throwPCException = true;
		} else {
			int sid = symbolicUtil.getDyscopeId(source, pointer);

			if (sid < 0) {
				errorLogger
						.logSimpleError(
								source,
								state,
								process,
								symbolicAnalyzer.stateInformation(state),
								ErrorKind.DEREFERENCE,
								"Attempt to dereference pointer into scope"
										+ " which has been removed from state: \npointer expression: "
										+ pointerExpression.toString()
										+ "\nevaluation: "
										+ this.symbolicAnalyzer
												.symbolicExpressionToString(
														source, state, null,
														pointer));
				throwPCException = true;
			} else {
				int vid = symbolicUtil.getVariableId(source, pointer);
				ReferenceExpression symRef = symbolicUtil.getSymRef(pointer);
				SymbolicExpression variableValue;

				if (!analysisOnly && checkOutput) {
					Variable variable = state.getDyscope(sid).lexicalScope()
							.variable(vid);

					if (variable.isOutput()) {
						errorLogger.logSimpleError(source, state, process,
								symbolicAnalyzer.stateInformation(state),
								ErrorKind.OUTPUT_READ,
								"Attempt to read output variable "
										+ variable.name().name());
						throwPCException = true;
					}
				}
				variableValue = state.getDyscope(sid).getValue(vid);
				if (!symRef.isIdentityReference() && variableValue.isNull()) {
					errorLogger.logSimpleError(source, state, process,
							symbolicAnalyzer.stateInformation(state),
							ErrorKind.UNDEFINED_VALUE,
							"Attempt to dereference a pointer that refers "
									+ "to an object with undefined value");
					throwPCException = true;
				}
				try {
					// this function should never return a java null
					deref = universe.dereference(variableValue, symRef);
				} catch (SARLException e) {
					errorLogger.logSimpleError(source, state, process,
							symbolicAnalyzer.stateInformation(state),
							ErrorKind.DEREFERENCE,
							"Illegal pointer dereference: " + e.getMessage());
					throwPCException = true;
				}
			}
		}
		if (throwPCException)
			throw new UnsatisfiablePathConditionException();
		else
			return new Evaluation(state, deref);
	}

	/**
	 * Evaluates the dynamic type of a given CIVL type at a certain state. When
	 * the CIVL type has some state, e.g., an array type with a variable as the
	 * extent, the type needs to be evaluated.
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the process where the computation happens.
	 * @param type
	 *            The CIVL type to be evaluated for the dynamic type.
	 * @param source
	 *            The source code element for error report.
	 * @param isDeclaration
	 *            The flag denoting if the type is part of a variable/function
	 *            declaration.
	 * @return The dynamic type of the given type.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation dynamicTypeOf(State state, int pid, CIVLType type,
			CIVLSource source, boolean isDeclaration)
			throws UnsatisfiablePathConditionException {
		TypeEvaluation typeEval = getDynamicType(state, pid, type, source,
				isDeclaration);
		SymbolicExpression expr = symbolicUtil.expressionOfType(type,
				typeEval.type);
		Evaluation result = new Evaluation(typeEval.state, expr);

		return result;
	}

	/**
	 * Evaluates an abstract function call.
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the process that the expression belongs to.
	 * @param expression
	 *            The abstract function call expression to be evaluated.
	 * @return The value of the expression and the new state.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateAbstractFunctionCall(State state, int pid,
			AbstractFunctionCallExpression expression)
			throws UnsatisfiablePathConditionException {
		AbstractFunction function = expression.function();
		SymbolicType returnType = function.returnType()
				.getDynamicType(universe);
		List<SymbolicType> argumentTypes = new ArrayList<SymbolicType>();
		List<SymbolicExpression> arguments = new ArrayList<SymbolicExpression>();
		SymbolicType functionType;
		SymbolicExpression functionExpression;
		SymbolicExpression functionApplication;
		Evaluation result;
		String functionName = function.name().name();

		for (Variable param : function.parameters()) {
			argumentTypes.add(param.type().getDynamicType(universe));
		}
		for (Expression arg : expression.arguments()) {
			Evaluation eval = evaluate(state, pid, arg);
			arguments.add(eval.value);
		}
		functionType = universe.functionType(argumentTypes, returnType);
		if (functionName.startsWith("$"))
			functionName = ABSTRACT_FUNCTION_PREFIX + functionName;
		functionExpression = universe.symbolicConstant(
				universe.stringObject(functionName), functionType);
		functionApplication = universe.apply(functionExpression, arguments);
		result = new Evaluation(state, functionApplication);
		return result;
	}

	/**
	 * Evaluates an address-of expression <code>&e</code>.
	 * 
	 * @param state
	 *            the pre-state
	 * @param pid
	 *            PID of the process performing the evaluation
	 * @param expression
	 *            the address-of expression
	 * @return the symbolic expression of pointer type resulting from evaluating
	 *         the address of the argument and a new state (if there is
	 *         side-effect, otherwise just return the original state)
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateAddressOf(State state, int pid,
			AddressOfExpression expression)
			throws UnsatisfiablePathConditionException {
		return reference(state, pid, expression.operand());
	}

	/**
	 * Evaluates a short-circuit "and" expression <code>p && q</code>.
	 * 
	 * @param state
	 *            the pre-state
	 * @param pid
	 *            PID of the process evaluating this expression
	 * @param expression
	 *            the and expression
	 * @return the result of applying the AND operator to the two arguments
	 *         together with the post-state whose path condition may contain the
	 *         side-effects resulting from evaluation
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateAnd(State state, int pid,
			BinaryExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.left());
		BooleanExpression leftValue = (BooleanExpression) eval.value;
		BooleanExpression assumption = eval.state.getPathCondition();
		Reasoner reasoner = universe.reasoner(assumption);

		// true && x = x;
		// TODO is it more efficient to call canonic before the valid call?
		if (reasoner.isValid(leftValue))
			return evaluate(eval.state, pid, expression.right());
		if (reasoner.isValid(universe.not(leftValue))) {
			// false && x = false;
			eval.value = universe.falseExpression();
			return eval;
		} else {
			BooleanExpression assumptionAndp = universe.and(assumption,
					leftValue);
			State s1 = eval.state.setPathCondition(assumptionAndp);
			Evaluation eval1 = evaluate(s1, pid, expression.right());
			BooleanExpression pcTemp = eval1.state.getPathCondition();

			if (!assumptionAndp.equals(pcTemp)) {
				BooleanExpression pc = universe.or(pcTemp,
						universe.and(assumption, universe.not(leftValue)));

				eval.state = eval.state.setPathCondition(pc);
			}
			// Reason for above: In the common case where there
			// are no side effects, this would set the path condition to
			// (assumption && p) || (assumption && !p),
			// which does not get simplified to just "assumption",
			// as one would like. So it is handled as a special case:
			// check whether pcTemp equals (assumption && p)
			// (i.e., the evaluation of expression.right() did not
			// add any side-effects). If this holds, then pc is just
			// assumption.
			// TODO check if assign to left
			eval.value = universe.and(leftValue,
					(BooleanExpression) eval1.value);
			return eval;
		}
	}

	/**
	 * Evaluates an array literal expression, like
	 * <code>{[1] = a, [2] = 3, [6]=9}</code>;
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The array literal expression.
	 * @return The symbolic representation of the array literal expression and
	 *         the new state if there is side effect.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateArrayLiteral(State state, int pid,
			ArrayLiteralExpression expression)
			throws UnsatisfiablePathConditionException {
		Expression[] elements = expression.elements();
		SymbolicType symbolicElementType;
		List<SymbolicExpression> symbolicElements = new ArrayList<>();
		Evaluation eval;

		for (Expression element : elements) {
			eval = evaluate(state, pid, element);
			symbolicElements.add(eval.value);
			state = eval.state;
		}
		// The symbolic element type is get from the function "getDynamicType()"
		// which won't give any information about extents, so we have to add it
		// if it's complete array type.
		if (expression.elementType() instanceof CIVLCompleteArrayType) {
			Pair<State, SymbolicType> pair;

			pair = getCompleteArrayType(state, pid,
					((CIVLCompleteArrayType) expression.elementType()));
			state = pair.left;
			symbolicElementType = pair.right;
		} else
			symbolicElementType = expression.elementType().getDynamicType(
					universe);
		return new Evaluation(state, universe.array(symbolicElementType,
				symbolicElements));
	}

	private Pair<State, SymbolicType> getCompleteArrayType(State state,
			int pid, CIVLCompleteArrayType elementType)
			throws UnsatisfiablePathConditionException {
		SymbolicType arrayType;
		Evaluation eval;
		Pair<State, SymbolicType> pair;

		if (elementType.elementType() instanceof CIVLCompleteArrayType) {
			pair = this.getCompleteArrayType(state, pid,
					(CIVLCompleteArrayType) elementType.elementType());
			state = pair.left;
			arrayType = pair.right;
		} else
			arrayType = elementType.elementType().getDynamicType(universe);
		eval = this.evaluate(state, pid, elementType.extent());
		state = eval.state;
		assert eval.value instanceof NumericExpression;
		return new Pair<State, SymbolicType>(state, universe.arrayType(
				arrayType, (NumericExpression) eval.value));
	}

	/**
	 * Evaluates a binary expression.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The PID of the currently executing process.
	 * @param process
	 *            The name of the process for error report.
	 * @param expression
	 *            The binary expression.
	 * @return A symbolic expression for the binary operation and a new state if
	 *         there is side-effect.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateBinary(State state, int pid, String process,
			BinaryExpression expression)
			throws UnsatisfiablePathConditionException {
		BINARY_OPERATOR operator = expression.operator();

		switch (operator) {
		case AND:
			return evaluateAnd(state, pid, expression);
		case AT:
			return this.evaluateRemoteExpression(state, pid, expression);
		case OR:
			return evaluateOr(state, pid, expression);
			// TODO code review
		case IMPLIES:
			return evaluateImplies(state, pid, expression);
		case BITAND:
			return evaluateBitand(state, pid, expression);
		case BITCOMPLEMENT:
			return evaluateBitcomplement(state, pid, expression);
		case BITOR:
			return evaluateBitor(state, pid, expression);
		case BITXOR:
			return evaluateBitxor(state, pid, expression);
		case SHIFTLEFT:
			return evaluateShiftleft(state, pid, expression);
		case SHIFTRIGHT:
			return evaluateShiftright(state, pid, expression);
		case DIVIDE:
		case LESS_THAN:
		case LESS_THAN_EQUAL:
		case MINUS:
		case MODULO:
		case PLUS:
		case POINTER_ADD:
		case POINTER_SUBTRACT:
		case TIMES:
			// numeric expression like +,-,*,/,%,etc
			if (expression.left().getExpressionType() != null
					&& expression.left().getExpressionType()
							.equals(typeFactory.scopeType())) {
				return evaluateScopeOperations(state, pid, expression);
			} else {
				return evaluateNumericOperations(state, pid, process,
						expression);
			}
		case NOT_EQUAL:
		case EQUAL:
			return evaluateNumericOperations(state, pid, process, expression);
		default:
			throw new CIVLUnimplementedFeatureException(
					"Evaluating binary operator of " + operator + " kind");
		}
	}

	/**
	 * Evaluates a bit and expression.
	 * 
	 * @param state
	 *            The state where the evaluation happens.
	 * @param pid
	 *            The PID of the process that triggers the evaluation.
	 * @param expression
	 *            The bit and expression to be evaluated.
	 * @return A possibly new state resulted from side effects during the
	 *         evaluation and the value of the bit and expression.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateBitand(State state, int pid,
			BinaryExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.left());
		SymbolicExpression left = eval.value, right, result;

		eval = evaluate(eval.state, pid, expression.right());
		right = eval.value;
		state = eval.state;
		result = universe.apply(this.bitAndFunc, Arrays.asList(left, right));
		return new Evaluation(state, result);
	}

	/**
	 * Evaluates a bit complement expression.
	 * 
	 * @param state
	 *            The state where the evaluation happens.
	 * @param pid
	 *            The PID of the process that triggers the evaluation.
	 * @param expression
	 *            The bit complement expression to be evaluated.
	 * @return A possibly new state resulted from side effects during the
	 *         evaluation and the value of the bit complement expression.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateBitcomplement(State state, int pid,
			BinaryExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.left());
		SymbolicExpression left = eval.value, right, result;

		eval = evaluate(eval.state, pid, expression.right());
		right = eval.value;
		state = eval.state;
		result = universe.apply(this.bitComplementFunc,
				Arrays.asList(left, right));
		return new Evaluation(state, result);
	}

	/**
	 * Evaluates a bit or expression.
	 * 
	 * @param state
	 *            The state where the evaluation happens.
	 * @param pid
	 *            The PID of the process that triggers the evaluation.
	 * @param expression
	 *            The bit or expression to be evaluated.
	 * @return A possibly new state resulted from side effects during the
	 *         evaluation and the value of the bit or expression.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateBitor(State state, int pid,
			BinaryExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.left());
		SymbolicExpression left = eval.value, right, result;

		eval = evaluate(eval.state, pid, expression.right());
		right = eval.value;
		state = eval.state;
		result = universe.apply(this.bitOrFunc, Arrays.asList(left, right));
		return new Evaluation(state, result);
	}

	/**
	 * Evaluates a bit xor expression.
	 * 
	 * @param state
	 *            The state where the evaluation happens.
	 * @param pid
	 *            The PID of the process that triggers the evaluation.
	 * @param expression
	 *            The bit xor expression to be evaluated.
	 * @return A possibly new state resulted from side effects during the
	 *         evaluation and the value of the bit xor expression.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateBitxor(State state, int pid,
			BinaryExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.left());
		SymbolicExpression left = eval.value, right, result;

		eval = evaluate(eval.state, pid, expression.right());
		right = eval.value;
		state = eval.state;
		result = universe.apply(this.bitXorFunc, Arrays.asList(left, right));
		return new Evaluation(state, result);
	}

	/**
	 * Evaluate a boolean literal expression.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The boolean literal expression.
	 * @return The symbolic representation of the boolean literal expression and
	 *         the new state if there is side effect during the evaluation.
	 */
	private Evaluation evaluateBooleanLiteral(State state, int pid,
			BooleanLiteralExpression expression) {
		return new Evaluation(state, universe.bool(expression.value()));
	}

	/**
	 * Evaluates a bound variable expression.
	 * 
	 * @param state
	 *            The state where the evaluation happens.
	 * @param pid
	 *            The PID of the process that triggers the evaluation.
	 * @param expression
	 *            The bound variable expression to be evaluated.
	 * @return A possibly new state resulted from side effects during the
	 *         evaluation and the value of the bound variable expression.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateBoundVariable(State state, int pid,
			BoundVariableExpression expression) {
		Iterator<SymbolicConstant> boundVariableIterator = boundVariables
				.iterator();
		Evaluation result = null;

		while (boundVariableIterator.hasNext()) {
			SymbolicConstant boundVariable = boundVariableIterator.next();

			if (boundVariable.name().toString()
					.equals(expression.name().name())) {
				result = new Evaluation(state, boundVariable);
				break;
			}
		}
		if (result != null) {
			return result;
		}
		throw new CIVLException("Unknown bound variable",
				expression.getSource());
	}

	/**
	 * Evaluates a cast expression.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param process
	 *            The process name for error report.
	 * @param expression
	 *            The cast expression.
	 * @return A possibly new state resulted from side effects during the
	 *         evaluation and the value of the cast expression.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateCast(State state, int pid, String process,
			CastExpression expression)
			throws UnsatisfiablePathConditionException {
		return this.evaluateCastWorker(state, pid, process,
				expression.getCastType(), expression.getExpression());
	}

	@Override
	public Evaluation evaluateCastWorker(State state, int pid, String process,
			CIVLType castType, Expression arg)
			throws UnsatisfiablePathConditionException {
		CIVLType argType = arg.getExpressionType();
		Evaluation eval = evaluate(state, pid, arg);
		SymbolicExpression value = eval.value;
		TypeEvaluation typeEval = getDynamicType(eval.state, pid, castType,
				arg.getSource(), false);
		SymbolicType endType = typeEval.type;

		state = typeEval.state;
		if (argType.isDomainType() && castType.isDomainType()) {
			return new Evaluation(state, value);
		} else if (argType.isBoolType() && castType.isIntegerType()) {
			eval.value = this.booleanToInteger(value);
			return eval;
		} else if (argType.isIntegerType() && castType.isPointerType()) {
			// only good cast for:
			// 1. from 0 to null pointer
			// 2. pointer2Int(x) back to x;
			BooleanExpression assumption = state.getPathCondition();
			BooleanExpression claim = universe.equals(zero, value);
			ResultType resultType = universe.reasoner(assumption).valid(claim)
					.getResultType();

			if (resultType != ResultType.YES) {
				SymbolicExpression castedValue = this.symbolicUtil
						.applyReverseFunction(POINTER_TO_INT_FUNCTION, value);

				if (castedValue != null)
					eval.value = castedValue;
				else if (((CIVLPointerType) castType).baseType().isVoidType()) {
					eval.value = value;
				} else {
					eval.value = universe.apply(this.int2PointerFunc,
							Arrays.asList(value));
					// state = errorLogger.logError(arg.getSource(), state,
					// process,
					// this.symbolicAnalyzer.stateInformation(state),
					// claim, resultType, ErrorKind.INVALID_CAST,
					// "Cast from non-zero integer to pointer");
					// eval.state = state;
				}
			} else
				eval.value = this.symbolicUtil.nullPointer();
			return eval;
		} else if (argType.isPointerType() && castType.isIntegerType()) {
			if (this.symbolicUtil.isNullPointer(value))
				eval.value = universe.integer(0);
			else if (value.type().equals(universe.integerType()))
				eval.value = value;
			else {
				SymbolicExpression castedValue = this.symbolicUtil
						.applyReverseFunction(INT_TO_POINTER_FUNCTION, value);

				if (castedValue != null)
					eval.value = castedValue;
				else
					eval.value = universe.apply(this.pointer2IntFunc,
							Arrays.asList(value));
			}
			return eval;
		} else if (argType.isPointerType() && castType.isPointerType()) {
			// pointer to pointer: for now...no change.
			return eval;
		} else if (argType.isIntegerType() && castType.isBoolType()) {
			if (value.type().isBoolean())
				eval.value = value;
			else
				eval.value = universe.not(universe.equals(value, zero));
			return eval;
		} else if (argType.isIntegerType() && castType.isCharType()) {
			NumericExpression integerValue = (NumericExpression) value;
			Number concreteValue = null;
			Reasoner reasoner = universe.reasoner(state.getPathCondition());
			CIVLSource source = arg.getSource();

			// If integerValue is concrete and is inside the range [0, 255],
			// return corresponding character by using java casting.
			// Else if it's only outside of the range [0, 255], return abstract
			// function.
			if (integerValue.operator() == SymbolicOperator.CONCRETE) {
				int int_value;

				concreteValue = symbolicUtil.extractInt(source, integerValue);
				assert (concreteValue != null) : "NumericExpression with concrete operator cannot "
						+ "provide concrete numeric value";
				assert (!(concreteValue instanceof IntegerNumber)) : "A Number object which suppose "
						+ "has integer type cannot cast to IntegerNumber type";
				int_value = concreteValue.intValue();
				if (int_value < 0 || int_value > 255) {
					throw new CIVLUnimplementedFeatureException(
							"Converting integer whose value is larger than UCHAR_MAX or is less than UCHAR_MIN to char type\n");
				} else
					eval.value = universe.character((char) int_value);
			} else {
				SymbolicExpression func;
				SymbolicFunctionType funcType;
				BooleanExpression insideRangeClaim;
				SymbolicExpression newCharValue;
				ResultType retType;

				// TODO change to andTo
				insideRangeClaim = universe.and(
						universe.lessThan(zero, integerValue),
						universe.lessThan(integerValue, universe.integer(255)));
				retType = reasoner.valid(insideRangeClaim).getResultType();
				if (retType == ResultType.YES) {
					// If not concrete, return abstract function.
					funcType = universe.functionType(
							Arrays.asList(universe.integerType()),
							universe.characterType());
					func = universe.canonic(universe.symbolicConstant(
							universe.stringObject("int2char"), funcType));
					newCharValue = universe.apply(func,
							Arrays.asList(integerValue));
					eval.value = newCharValue;
				} else {
					// Certainty certain;
					//
					// if (retType == ResultType.MAYBE)
					// certain = Certainty.MAYBE;
					// else
					// certain = Certainty.PROVEABLE;
					eval.state = errorLogger
							.logError(
									source,
									state,
									process,
									this.symbolicAnalyzer
											.stateInformation(state),
									insideRangeClaim,
									retType,
									ErrorKind.INVALID_CAST,
									"Cast operation may involve casting a integer, "
											+ "whose value is larger than UCHAR_MAX or less than UCHAR_MIN, "
											+ "to char type object which is considered as unimplemented feature of CIVL");
					throw new UnsatisfiablePathConditionException();
				}

			}
			return eval;
		}
		try {
			eval.value = universe.cast(endType, eval.value);
		} catch (SARLException e) {
			errorLogger.logSimpleError(arg.getSource(), state, process,
					this.symbolicAnalyzer.stateInformation(state),
					ErrorKind.INVALID_CAST, "SARL could not cast: " + e);
			throw new UnsatisfiablePathConditionException();
		}
		return eval;
	}

	/**
	 * Evaluates a char literal expression.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The char literal expression.
	 * @return A possibly new state resulted from side effects during the
	 *         evaluation and the value of the char literal expression.
	 */
	private Evaluation evaluateCharLiteral(State state, int pid,
			CharLiteralExpression expression) {
		return new Evaluation(state, universe.character(expression.value()));
	}

	/**
	 * Evaluates a dereference expression <code>*e</code>.
	 * 
	 * @param state
	 *            the pre-state
	 * @param pid
	 *            PID of the process performing the evaluation
	 * @param process
	 *            The process name for error report.
	 * @param expression
	 *            the dereference expression
	 * @return the evaluation with the properly updated state and the value
	 *         after the dereference.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateDereference(State state, int pid,
			String process, DereferenceExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.pointer());

		if (eval.value.isNull()) {
			this.errorLogger.logSimpleError(expression.pointer().getSource(),
					state, process, symbolicAnalyzer.stateInformation(state),
					ErrorKind.UNDEFINED_VALUE,
					"attempt to dereference an uninitialized pointer");
			throw new UnsatisfiablePathConditionException();
		}
		return dereference(expression.pointer().getSource(), eval.state,
				process, expression.pointer(), eval.value, true);
	}

	/**
	 * Evaluates a derivative call expression.
	 * 
	 * @param state
	 *            the pre-state
	 * @param pid
	 *            the PID of the process running this call
	 * @param expression
	 *            the derivative call expression to be evaluated
	 * @return the evaluation with the properly updated state and the value of
	 *         the derivative call expression.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateDerivativeCall(State state, int pid,
			DerivativeCallExpression expression)
			throws UnsatisfiablePathConditionException {
		AbstractFunction function = expression.function();
		SymbolicType returnType = function.returnType()
				.getDynamicType(universe);
		List<SymbolicType> argumentTypes = new ArrayList<SymbolicType>();
		List<SymbolicExpression> arguments = new ArrayList<SymbolicExpression>();
		SymbolicType functionType;
		SymbolicExpression functionExpression;
		SymbolicExpression functionApplication;
		Evaluation result;
		String derivativeName;

		for (Variable param : function.parameters()) {
			argumentTypes.add(param.type().getDynamicType(universe));
		}
		for (Expression arg : expression.arguments()) {
			Evaluation eval = evaluate(state, pid, arg);
			arguments.add(eval.value);
		}
		functionType = universe.functionType(argumentTypes, returnType);
		// The derivative name is the name of the function concatenated with the
		// names and degrees of the partials. e.g. the name of
		// $D[rho,{x,1},{y,2}]() is "rhox1y2"
		derivativeName = function.name().name();
		for (Pair<Variable, IntegerLiteralExpression> partial : expression
				.partials()) {
			derivativeName += partial.left.name().name()
					+ partial.right.value();
		}
		functionExpression = universe.symbolicConstant(
				universe.stringObject(derivativeName), functionType);
		functionApplication = universe.apply(functionExpression, arguments);
		result = new Evaluation(state, functionApplication);
		return result;
	}

	/**
	 * Evaluates a domain guard expression, the value of which is true iff there
	 * is a subsequent element of of the current one in the domain object. See
	 * also {@link DomainGuardExpression}.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param domainGuard
	 *            The domain guard expression to be evaluated, which contains
	 *            the information of the current domain element and the domain
	 *            object.
	 * @return the evaluation with the properly updated state and the value of
	 *         the domain guard expression.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateDomainGuard(State state, int pid,
			DomainGuardExpression domainGuard)
			throws UnsatisfiablePathConditionException {
		Expression domain = domainGuard.domain();
		int dimension = domainGuard.dimension();
		// Collection for storing given domain element.
		List<SymbolicExpression> domElement = new LinkedList<>();
		SymbolicExpression domainValue;
		// The value of the domain union.
		SymbolicExpression domainUnion;
		Evaluation eval = this.evaluate(state, pid, domain);
		// Result, if there is a subsequence.
		boolean hasNext = false;
		// Flag indicating the given domain element only contains NULLs.
		boolean isAllNull = true;

		state = eval.state;
		domainValue = eval.value;
		domainUnion = universe.tupleRead(domainValue, twoObj);
		// Evaluating the value of the given element.
		for (int i = 0; i < dimension; i++) {
			SymbolicExpression varValue = state.valueOf(pid,
					domainGuard.variableAt(i));

			domElement.add(varValue);
			if (!varValue.isNull())
				isAllNull = false;
		}
		// If the domain object is a rectangular domain
		if (symbolicUtil.isRectangularDomain(domainValue)) {
			SymbolicExpression recDom = universe.unionExtract(zeroObj,
					domainUnion);

			if (isAllNull)
				hasNext = !symbolicUtil.isEmptyDomain(domainValue, dimension,
						domain.getSource());
			else
				hasNext = symbolicUtil.recDomainHasNext(recDom, dimension,
						domElement);
			eval.state = state;
			// TODO:rectangular domain always has concrete ranges so that the
			// result is always concrete ?
			eval.value = universe.bool(hasNext);
		} else if (symbolicUtil.isLiteralDomain(domainValue)) {
			Variable literalDomCounterVar;

			// TODO: is there a domain that contains none elements ?
			if (isAllNull)
				hasNext = !symbolicUtil.isEmptyDomain(domainValue, dimension,
						domain.getSource());
			else {
				NumericExpression literalCounter;
				NumericExpression domainSize = symbolicUtil
						.getDomainSize(domainValue);
				int counter, size;

				// Compare the literal domain counter and the size of the
				// domain.
				literalDomCounterVar = domainGuard.getLiteralDomCounter();
				literalCounter = (NumericExpression) state.valueOf(pid,
						literalDomCounterVar);
				counter = ((IntegerNumber) universe
						.extractNumber(literalCounter)).intValue();
				size = ((IntegerNumber) universe.extractNumber(domainSize))
						.intValue();
				hasNext = counter < size;
			}
		} else
			throw new CIVLInternalException(
					"A domain object is neither a rectangular domain nor a literal domain",
					domainGuard.getSource());
		eval.state = state;
		eval.value = universe.bool(hasNext);
		return eval;
	}

	/**
	 * Evaluates the value of a rectangular domain literal expression.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param recDomain
	 *            The expression of the rectangular domain
	 * @return The evaluation with the properly updated state and the value of
	 *         the rectangular domain literal expression.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateRecDomainLiteral(State state, int pid,
			RecDomainLiteralExpression recDomain)
			throws UnsatisfiablePathConditionException {
		int dim = recDomain.dimension();
		List<SymbolicExpression> ranges = new ArrayList<>();
		Evaluation eval;
		SymbolicExpression domainV;
		SymbolicType domainType;
		// For a rectangular domain, its range types are all the same.
		// because rectangular domain is an array of ranges
		SymbolicType rangeType;
		List<SymbolicExpression> domValueComponents = new LinkedList<>();
		// ranges should be in form of an array inside a domain.
		SymbolicExpression rangesArray;
		CIVLDomainType civlDomType;
		CIVLType civlRangeType;

		for (int i = 0; i < dim; i++) {
			eval = evaluate(state, pid, recDomain.rangeAt(i));
			state = eval.state;
			ranges.add(eval.value);
		}
		rangeType = ranges.get(0).type();
		civlRangeType = typeFactory.rangeType();
		civlDomType = typeFactory.domainType(civlRangeType);
		domainType = civlDomType.getDynamicType(universe);
		assert domainType instanceof SymbolicTupleType : "Dynamic $domain type is not a tuple type";
		assert rangeType instanceof SymbolicTupleType : "Dynamic $range type is not a tuple type";
		// Adding components
		domValueComponents.add(universe.integer(dim));
		// Union field index which indicates it's a rectangular domain.
		domValueComponents.add(zero);
		rangesArray = universe.array(rangeType, ranges);
		domValueComponents.add(universe.unionInject(
				civlDomType.getDynamicSubTypesUnion(universe), zeroObj,
				rangesArray));
		// The cast is guaranteed
		// TODO: when is the appropriate time to call universe.canonic() ?
		domainV = universe.canonic(universe.tuple(
				(SymbolicTupleType) domainType, domValueComponents));
		return new Evaluation(state, domainV);
	}

	/**
	 * Evaluates a "dot" expression used to navigate to a field in a record,
	 * <code>e.f</code>.
	 * 
	 * @param state
	 *            The state of the model
	 * @param pid
	 *            The PID of the process evaluating this expression
	 * @param expression
	 *            The dot expression to evaluated
	 * @return The evaluation which contains the result of evaluating the
	 *         expression together with the post-state which may incorporate
	 *         side-effects resulting from the evaluation
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateDot(State state, int pid, String process,
			DotExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.structOrUnion());
		SymbolicExpression structValue = eval.value;
		int fieldIndex = expression.fieldIndex();

		if (expression.isStruct()) {
			eval.value = universe.tupleRead(structValue,
					universe.intObject(fieldIndex));
		} else {
			BooleanExpression test = universe.unionTest(
					universe.intObject(fieldIndex), structValue);

			if (test.isFalse()) {
				errorLogger.logSimpleError(expression.getSource(), eval.state,
						process, this.symbolicAnalyzer.stateInformation(state),
						ErrorKind.UNION,
						"Attempt to access an invalid union member");
				throw new UnsatisfiablePathConditionException();
			}
			eval.value = universe.unionExtract(universe.intObject(fieldIndex),
					structValue);
		}
		return eval;
	}

	/**
	 * Evaluates a dynamic type of expression. TODO what's this for?
	 * 
	 * @param state
	 * @param pid
	 * @param expression
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateDynamicTypeOf(State state, int pid,
			DynamicTypeOfExpression expression)
			throws UnsatisfiablePathConditionException {
		return dynamicTypeOf(state, pid, expression.getType(),
				expression.getSource(), true);
	}

	/**
	 * Evaluates a function guard expression. When the function is a system
	 * function, the evaluation inquires the corresponding library for its
	 * evaluation; otherwise, the result is always the true value.
	 * 
	 * @param state
	 * @param pid
	 * @param process
	 * @param expression
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateFunctionGuard(State state, int pid,
			String process, FunctionGuardExpression expression)
			throws UnsatisfiablePathConditionException {
		Triple<State, CIVLFunction, Integer> eval = this
				.evaluateFunctionIdentifier(state, pid,
						expression.functionExpression(), expression.getSource());
		CIVLFunction function;

		state = eval.first;
		function = eval.second;
		if (function == null) {
			errorLogger.logSimpleError(expression.getSource(), state, process,
					symbolicAnalyzer.stateInformation(state), ErrorKind.OTHER,
					"function body cann't be found");
			throw new UnsatisfiablePathConditionException();
		}
		if (function.isRootFunction()) {
			SystemFunction systemFunction = (SystemFunction) function;

			return getSystemGuard(expression.getSource(), state, pid,
					systemFunction.getLibrary(), systemFunction.name().name(),
					expression.arguments());
		}
		return new Evaluation(state, universe.trueExpression());
	}

	private Evaluation evaluateFunctionIdentifierExpression(State state,
			int pid, FunctionIdentifierExpression expression) {
		Scope scope = expression.scope();
		SymbolicExpression dyScopeId = modelFactory.scopeValue(state
				.getDyscope(pid, scope));
		SymbolicExpression functionPointer = universe.tuple(
				this.functionPointerType,
				Arrays.asList(dyScopeId,
						universe.integer(expression.function().fid())));

		return new Evaluation(state, functionPointer);
	}

	private Evaluation evaluateHereOrRootScope(State state, int pid,
			HereOrRootExpression expression) {
		int dyScopeID = expression.isRoot() ? state.rootDyscopeID() : state
				.getProcessState(pid).getDyscopeId();

		return new Evaluation(state, modelFactory.scopeValue(dyScopeID));
	}

	/**
	 * Evaluates a short-circuit "implies" expression "p=?q".
	 * 
	 * @param state
	 *            the pre-state
	 * @param pid
	 *            PID of the process evaluating this expression
	 * @param expression
	 *            the and expression
	 * @return the result of applying the IMPLIES operator to the two arguments
	 *         together with the post-state whose path condition may contain the
	 *         side-effects resulting from evaluation
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateImplies(State state, int pid,
			BinaryExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.left());
		BooleanExpression p = (BooleanExpression) eval.value;
		BooleanExpression assumption = eval.state.getPathCondition();
		Reasoner reasoner = universe.reasoner(assumption);

		// If p is false, the implication will evaluate to true.
		if (reasoner.isValid(universe.not(p))) {
			eval.value = universe.trueExpression();
			return eval;
		} else {
			State s1 = eval.state.setPathCondition(universe.and(assumption, p));
			Evaluation eval1 = evaluate(s1, pid, expression.right());
			BooleanExpression pc = universe.or(eval1.state.getPathCondition(),
					universe.and(assumption, p));

			eval.state = eval.state.setPathCondition(pc);
			eval.value = universe.implies(p, (BooleanExpression) eval1.value);
			return eval;
		}
	}

	/**
	 * Evaluates an initial value expression.
	 * 
	 * @param state
	 * @param pid
	 * @param expression
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateInitialValue(State state, int pid,
			InitialValueExpression expression)
			throws UnsatisfiablePathConditionException {
		Variable variable = expression.variable();
		CIVLType type = variable.type();
		TypeEvaluation typeEval = getDynamicType(state, pid, type,
				expression.getSource(), false);
		int sid = typeEval.state.getDyscopeID(pid, variable);

		return computeInitialValue(typeEval.state, pid, variable,
				typeEval.type, sid);
	}

	/**
	 * Computes the symbolic initial value of a variable.
	 * 
	 * @param state
	 *            The state where the computation happens.
	 * @param pid
	 *            The PID of the process that triggers the computation.
	 * @param variable
	 *            The variable to be evaluated.
	 * @param dynamicType
	 *            The symbolic type of the variable.
	 * @param dyscopeId
	 *            The dynamic scope ID of the current state.
	 * @return The symbolic initial value of the given variable
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation computeInitialValue(State state, int pid,
			Variable variable, SymbolicType dynamicType, int dyscopeId)
			throws UnsatisfiablePathConditionException {
		CIVLType type = variable.type();
		int vid = variable.vid();
		SymbolicExpression result;

		if (!variable.isInput() && variable.isStatic()) {
			return initialValueOfType(state, pid, type);
		} else if (!variable.isInput()
				&& !variable.isBound()
				&& (type instanceof CIVLPrimitiveType || type.isPointerType() || type
						.isDomainType())) {
			result = nullExpression;
		} else {// the case of an input variable or a variable of
			// array/struct/union type.
			String name;
			StringObject nameObj;

			if (variable.scope().id() == 0 && variable.isInput()) {
				name = "X" + stateFactory.numSymbolicConstants(state);
				state = stateFactory.incrementNumSymbolicConstants(state);
			} else
				name = "X_s" + dyscopeId + "v" + vid + "p" + pid;
			nameObj = universe.stringObject(name);
			result = universe.symbolicConstant(nameObj, dynamicType);
		}
		return new Evaluation(state, result);
	}

	/**
	 * Evaluates an integer literal expression.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The integer literal expression.
	 * @return The symbolic representation of the integer literal expression.
	 */
	private Evaluation evaluateIntegerLiteral(State state, int pid,
			IntegerLiteralExpression expression) {
		return new Evaluation(state, universe.integer(expression.value()
				.intValue()));
	}

	private Evaluation evaluateNumericOperations(State state, int pid,
			String process, BinaryExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.left());
		SymbolicExpression left = eval.value;
		SymbolicExpression right;

		eval = evaluate(eval.state, pid, expression.right());
		right = eval.value;
		switch (expression.operator()) {
		case PLUS:
			eval.value = universe.add((NumericExpression) left,
					(NumericExpression) right);
			break;
		case MINUS:
			eval.value = universe.subtract((NumericExpression) left,
					(NumericExpression) right);
			break;
		case TIMES:
			eval.value = universe.multiply((NumericExpression) left,
					(NumericExpression) right);
			break;
		case DIVIDE: {
			BooleanExpression assumption = eval.state.getPathCondition();
			NumericExpression denominator = (NumericExpression) right;

			if (this.civlConfig.checkDivisionByZero()) {
				BooleanExpression claim = universe.neq(
						zeroOf(expression.getSource(),
								expression.getExpressionType()), denominator);
				ResultType resultType = universe.reasoner(assumption)
						.valid(claim).getResultType();

				if (resultType != ResultType.YES) {
					Expression divisor = expression.right();

					eval.state = errorLogger
							.logError(
									expression.getSource(),
									eval.state,
									process,
									this.symbolicAnalyzer
											.stateInformation(eval.state),
									claim,
									resultType,
									ErrorKind.DIVISION_BY_ZERO,
									"division by zero where divisor: "
											+ expression.right()
											+ "="
											+ this.symbolicAnalyzer
													.symbolicExpressionToString(
															divisor.getSource(),
															state,
															divisor.getExpressionType(),
															right));
					throw new UnsatisfiablePathConditionException();
				}
			}
			eval.value = universe.divide((NumericExpression) left, denominator);
		}
			break;
		case LESS_THAN:
			eval.value = universe.lessThan((NumericExpression) left,
					(NumericExpression) right);
			break;
		case LESS_THAN_EQUAL:
			eval.value = universe.lessThanEquals((NumericExpression) left,
					(NumericExpression) right);
			break;
		// equal and not_equal operators support scope, process, and pointer
		// types. If the value of those types is undefined (e.g., process -1,
		// scope -1, pointer<-1, ..., ...>), an error should be reported.
		case EQUAL: {
			SymbolicType leftType = left.type(), rightType = right.type();

			this.isValueDefined(eval.state, process, expression.left(), left);
			this.isValueDefined(eval.state, process, expression.right(), right);
			if (leftType.isBoolean() && rightType.isInteger()) {
				left = booleanToInteger(left);
			} else if (leftType.isInteger() && rightType.isBoolean()) {
				right = booleanToInteger(right);
			}
			eval.value = universe.equals(left, right);
			break;
		}
		case NOT_EQUAL: {
			SymbolicType leftType = left.type(), rightType = right.type();

			this.isValueDefined(eval.state, process, expression.left(), left);
			this.isValueDefined(eval.state, process, expression.right(), right);
			if (leftType.isBoolean() && rightType.isInteger()) {
				left = booleanToInteger(left);
			} else if (leftType.isInteger() && rightType.isBoolean()) {
				right = booleanToInteger(right);
			}
			eval.value = universe.neq(left, right);
			break;
		}
		case MODULO: {
			BooleanExpression assumption = eval.state.getPathCondition();
			NumericExpression denominator = (NumericExpression) right;

			if (!this.civlConfig.svcomp()) {
				BooleanExpression claim = universe.neq(
						zeroOf(expression.getSource(),
								expression.getExpressionType()), denominator);
				ResultType resultType = universe.reasoner(assumption)
						.valid(claim).getResultType();

				// TODO: check not negative
				if (resultType != ResultType.YES) {
					eval.state = errorLogger.logError(expression.getSource(),
							eval.state, process,
							this.symbolicAnalyzer.stateInformation(eval.state),
							claim, resultType, ErrorKind.DIVISION_BY_ZERO,
							"Modulus denominator is zero");
					throw new UnsatisfiablePathConditionException();
				}
			}
			eval.value = universe.modulo((NumericExpression) left, denominator);
			break;
		}
		case POINTER_ADD:
			eval = pointerAdd(eval.state, pid, process, expression, left,
					(NumericExpression) right);
			break;
		case POINTER_SUBTRACT: {
			if (right.isNumeric())
				eval = this.pointerAdd(state, pid, process, expression, left,
						universe.minus((NumericExpression) right));
			else
				eval = pointerSubtraction(eval.state, pid, process, expression,
						left, right);
			break;

		}
		case IMPLIES:
		case AND:
		case OR:
			throw new CIVLInternalException("unreachable", expression);
		default:
			throw new CIVLUnimplementedFeatureException(
					"Evaluating numeric operator " + expression.operator(),
					expression);
		}
		return eval;
	}

	private SymbolicExpression booleanToInteger(SymbolicExpression booleanValue) {
		if (booleanValue.isTrue())
			return one;
		else if (booleanValue.isFalse())
			return zero;
		else
			return this.universe.cond((BooleanExpression) booleanValue, one,
					zero);
	}

	/**
	 * Evaluates a short-circuit "or" expression "p||q".
	 * 
	 * @param state
	 *            the pre-state
	 * @param pid
	 *            PID of the process evaluating this expression
	 * @param expression
	 *            the OR expression
	 * @return the result of applying the OR operator to the two arguments
	 *         together with the post-state whose path condition may contain the
	 *         side-effects resulting from evaluation
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateOr(State state, int pid,
			BinaryExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.left());
		BooleanExpression p = (BooleanExpression) eval.value;
		BooleanExpression assumption = eval.state.getPathCondition();
		Reasoner reasoner = universe.reasoner(assumption);

		// TODO: handle special common case as in evaluateAnd.
		// Look at evaluation of ternary operator too?

		if (reasoner.isValid(p)) {
			eval.value = universe.trueExpression();
			return eval;
		}
		if (reasoner.isValid(universe.not(p))) {
			return evaluate(eval.state, pid, expression.right());
		} else {
			State s1 = eval.state.setPathCondition(universe.and(assumption,
					universe.not(p)));
			Evaluation eval1 = evaluate(s1, pid, expression.right());
			BooleanExpression pc = universe.or(eval1.state.getPathCondition(),
					universe.and(assumption, p));

			eval.state = eval.state.setPathCondition(pc);
			// TODO change to orTo
			eval.value = universe.or(p, (BooleanExpression) eval1.value);
			return eval;
		}
	}

	private Evaluation evaluateQuantifiedExpression(State state, int pid,
			QuantifiedExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation result;
		Evaluation quantifiedExpression;
		BooleanExpression context;
		Reasoner reasoner;
		BooleanExpression simplifiedExpression;
		SymbolicConstant boundVariable = universe.symbolicConstant(expression
				.boundVariableName().stringObject(), expression
				.boundVariableType().getDynamicType(universe));
		State stateWithRestriction;

		boundVariables.push(boundVariable);
		if (expression.isRange()) {
			Evaluation lower = evaluate(state, pid, expression.lower());
			Evaluation upper = evaluate(state, pid, expression.upper());
			SymbolicExpression rangeRestriction;
			NumericExpression upperBound;

			assert lower.value instanceof NumericExpression;
			assert upper.value instanceof NumericExpression;
			upperBound = universe.add(one, (NumericExpression) upper.value);
			// TODO change to andTo
			rangeRestriction = universe.and(universe.lessThanEquals(
					(NumericExpression) lower.value,
					(NumericExpression) boundVariable), universe
					.lessThanEquals((NumericExpression) boundVariable,
							(NumericExpression) upper.value));
			// TODO change to andTo
			stateWithRestriction = state.setPathCondition(universe.and(
					(BooleanExpression) rangeRestriction,
					state.getPathCondition()));
			quantifiedExpression = evaluate(stateWithRestriction, pid,
					expression.expression());
			switch (expression.quantifier()) {
			case EXISTS:
				result = new Evaluation(state, universe.existsInt(
						(NumericSymbolicConstant) boundVariable,
						(NumericExpression) lower.value, upperBound,
						(BooleanExpression) quantifiedExpression.value));
				break;
			case FORALL:
				result = new Evaluation(state, universe.forallInt(
						(NumericSymbolicConstant) boundVariable,
						(NumericExpression) lower.value, upperBound,
						(BooleanExpression) quantifiedExpression.value));
				break;
			case UNIFORM:
				result = new Evaluation(state, universe.forallInt(
						(NumericSymbolicConstant) boundVariable,
						(NumericExpression) lower.value, upperBound,
						(BooleanExpression) quantifiedExpression.value));
				break;
			default:
				throw new CIVLException("Unknown quantifier ",
						expression.getSource());
			}
		} else {
			Evaluation restriction = evaluate(state, pid,
					expression.boundRestriction());
			stateWithRestriction = state.setPathCondition(universe.and(
					(BooleanExpression) restriction.value,
					state.getPathCondition()));
			quantifiedExpression = evaluate(stateWithRestriction, pid,
					expression.expression());
			// By definition, the restriction should be boolean valued.
			assert restriction.value instanceof BooleanExpression;
			context = universe.and(state.getPathCondition(),
					(BooleanExpression) restriction.value);
			reasoner = universe.reasoner(context);
			simplifiedExpression = (BooleanExpression) reasoner
					.simplify(quantifiedExpression.value);
			switch (expression.quantifier()) {
			case EXISTS:
				result = new Evaluation(state, universe.exists(boundVariable,
						universe.and((BooleanExpression) restriction.value,
								simplifiedExpression)));
				break;
			case FORALL:
				result = new Evaluation(state, universe.forall(boundVariable,
						universe.implies((BooleanExpression) restriction.value,
								simplifiedExpression)));
				break;
			case UNIFORM:
				result = new Evaluation(state, universe.forall(boundVariable,
						universe.implies((BooleanExpression) restriction.value,
								simplifiedExpression)));
				break;
			default:
				throw new CIVLException("Unknown quantifier ",
						expression.getSource());
			}
		}
		boundVariables.pop();
		return result;
	}

	/**
	 * the rule of remote accessing is the remote variable is reachable from the
	 * current scope where the remote process is now in.
	 * 
	 * @param state
	 * @param pid
	 * @param expression
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateRemoteExpression(State state, int pid,
			BinaryExpression expression)
			throws UnsatisfiablePathConditionException {
		String process = state.getProcessState(pid).name() + "(id = " + pid
				+ ")";
		Evaluation eval;
		SymbolicExpression symProc, value = null;
		int remotePid;
		int dyscopeId;
		int vid = -1;
		Expression processExpr = expression.right();
		VariableExpression variableExpr = (VariableExpression) expression
				.left();
		Variable variable = null;

		eval = this.evaluate(state, pid, processExpr);
		state = eval.state;
		symProc = eval.value;
		// If the process expression is not a NumericExpression, report the
		// error.
		if (!(symProc instanceof NumericExpression)) {
			errorLogger.logSimpleError(expression.getSource(), state, process,
					symbolicAnalyzer.stateToString(state), ErrorKind.OTHER,
					"The right-hand side expression of a remote access "
							+ " must be a numeric expression.");
			throw new UnsatisfiablePathConditionException();
		}
		remotePid = ((IntegerNumber) universe
				.extractNumber((NumericExpression) symProc)).intValue();
		dyscopeId = state.getProcessState(remotePid).getDyscopeId();
		variable = variableExpr.variable();
		while (dyscopeId != -1) {
			Scope scope1 = state.getDyscope(dyscopeId).lexicalScope();

			if (scope1.containsVariable(variable.name().name())) {
				vid = scope1.variable(variable.name()).vid();
				break;
			}
			dyscopeId = state.getParentId(dyscopeId);
		}
		if (dyscopeId != -1 && vid != -1)
			value = state.getVariableValue(dyscopeId, vid);
		else {
			this.errorLogger.logSimpleError(expression.getSource(), state,
					process, symbolicAnalyzer.stateToString(state),
					ErrorKind.OTHER,
					"Remote access failure: The remote variable "
							+ variableExpr.toString()
							+ "doesn't reachable by the remote process:"
							+ remotePid);
			throw new UnsatisfiablePathConditionException();
		}
		if (value == null)
			throw new UnsatisfiablePathConditionException();
		eval = new Evaluation(state, value);
		return eval;
	}

	private Evaluation evaluateRegularRange(State state, int pid,
			RegularRangeExpression range)
			throws UnsatisfiablePathConditionException {
		SymbolicTupleType type = (SymbolicTupleType) range.getExpressionType()
				.getDynamicType(universe);
		Evaluation eval = this.evaluate(state, pid, range.getLow());
		SymbolicExpression low, high, step, rangeValue;
		BooleanExpression claim;
		boolean negativeStep = false;
		ResultType validity;
		String process = state.getProcessState(pid).name() + "(id = " + pid
				+ ")";

		low = eval.value;
		state = eval.state;
		eval = evaluate(state, pid, range.getHigh());
		high = eval.value;
		state = eval.state;
		eval = evaluate(state, pid, range.getStep());
		step = eval.value;
		state = eval.state;
		claim = universe.equals(this.zero, step);
		validity = universe.reasoner(state.getPathCondition()).valid(claim)
				.getResultType();
		if (validity == ResultType.YES) {
			errorLogger.logSimpleError(range.getSource(), state, process,
					symbolicAnalyzer.stateInformation(state), ErrorKind.OTHER,
					"a regular range expression requires a non-zero step");
			throw new UnsatisfiablePathConditionException();
		}
		claim = universe.lessThan(this.zero, (NumericExpression) step);
		validity = universe.reasoner(state.getPathCondition()).valid(claim)
				.getResultType();
		if (validity == ResultType.NO)
			negativeStep = true;
		if (negativeStep) {
			SymbolicExpression tmp = low;

			low = high;
			high = tmp;
		}
		rangeValue = universe.tuple(type, Arrays.asList(low, high, step));
		return new Evaluation(state, rangeValue);
	}

	private Evaluation evaluateScopeOperations(State state, int pid,
			BinaryExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.left());
		int left = modelFactory.getScopeId(expression.left().getSource(),
				eval.value);
		int right;
		boolean result;

		state = eval.state;
		eval = evaluate(state, pid, expression.right());
		state = eval.state;
		right = modelFactory.getScopeId(expression.right().getSource(),
				eval.value);
		switch (expression.operator()) {
		case PLUS:
			int lowestCommonAncestor = stateFactory.lowestCommonAncestor(state,
					left, right);

			eval.value = modelFactory.scopeValue(lowestCommonAncestor);
			break;
		case LESS_THAN:
			result = stateFactory.isDescendantOf(state, right, left);
			eval.value = universe.bool(result);
			break;
		case LESS_THAN_EQUAL:
			result = (left == right) ? true : stateFactory.isDescendantOf(
					state, right, left);
			eval.value = universe.bool(result);
			break;
		case EQUAL:
			eval.value = universe.bool(left == right);
			break;
		case NOT_EQUAL:
			eval.value = universe.bool(left != right);
			break;
		default:
			throw new CIVLUnimplementedFeatureException(
					"evaluting scope operator " + expression.operator(),
					expression.getSource());
		}
		return eval;
	}

	private Evaluation evaluateSizeofExpressionExpression(State state, int pid,
			SizeofExpression expression)
			throws UnsatisfiablePathConditionException {
		return evaluateSizeofType(expression.getSource(), state, pid,
				expression.getArgument().getExpressionType());
	}

	private Evaluation evaluateSizeofTypeExpression(State state, int pid,
			SizeofTypeExpression expression)
			throws UnsatisfiablePathConditionException {
		return evaluateSizeofType(expression.getSource(), state, pid,
				expression.getTypeArgument());
	}

	/**
	 * Evaluate a subscript expression.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The array index expression.
	 * @return A symbolic expression for an array read.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateSubscript(State state, int pid, String process,
			SubscriptExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.array());
		SymbolicExpression array = eval.value;
		SymbolicArrayType arrayType = (SymbolicArrayType) array.type();
		NumericExpression index;

		eval = evaluate(state, pid, expression.index());
		index = (NumericExpression) eval.value;
		eval.state = this
				.checkArrayIndexInBound(eval.state, expression.getSource(),
						process, arrayType, array, index, false);
		eval.value = universe.arrayRead(array, index);
		return eval;
	}

	private State checkArrayIndexInBound(State state, CIVLSource source,
			String process, SymbolicArrayType arrayType,
			SymbolicExpression array, NumericExpression index,
			boolean addressOnly) throws UnsatisfiablePathConditionException {
		if (!this.civlConfig.svcomp() && arrayType.isComplete()) {
			NumericExpression length = universe.length(array);
			BooleanExpression assumption = state.getPathCondition();
			// TODO change to andTo
			BooleanExpression claim;

			if (addressOnly)
				claim = universe.and(universe.lessThanEquals(zero, index),
						universe.lessThanEquals(index, length));
			else
				claim = universe.and(universe.lessThanEquals(zero, index),
						universe.lessThan(index, length));

			ResultType resultType = universe.reasoner(assumption).valid(claim)
					.getResultType();

			if (resultType != ResultType.YES) {
				state = errorLogger.logError(source, state, process,
						symbolicAnalyzer.stateInformation(state), claim,
						resultType, ErrorKind.OUT_OF_BOUNDS,
						"Out of bounds array index:\nindex = " + index
								+ "\nlength = " + length);
				throw new UnsatisfiablePathConditionException();
			}
		}
		return state;
	}

	private Evaluation evaluateSelf(State state, int pid,
			SelfExpression expression) {
		return new Evaluation(state, modelFactory.processValue(pid));
	}

	private Evaluation evaluateProcnull(State state, int pid,
			ProcnullExpression expression) {
		return new Evaluation(state, modelFactory.nullProcessValue());
	}

	/**
	 * Evaluate a real literal expression.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The real literal expression.
	 * @return The symbolic representation of the real literal expression.
	 */
	private Evaluation evaluateRealLiteral(State state, int pid,
			RealLiteralExpression expression) {
		return new Evaluation(state, universe.number(universe
				.numberObject(numberFactory.rational(expression.value()
						.toPlainString()))));
	}

	private Evaluation evaluateScopeofExpression(State state, int pid,
			String process, ScopeofExpression expression)
			throws UnsatisfiablePathConditionException {
		LHSExpression argument = expression.argument();

		return evaluateScopeofExpressionWorker(state, pid, process, argument);
	}

	private Evaluation evaluateScopeofExpressionWorker(State state, int pid,
			String process, LHSExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval;

		switch (expression.lhsExpressionKind()) {
		case DEREFERENCE:
			Expression pointer = ((DereferenceExpression) expression).pointer();

			eval = evaluate(state, pid, pointer);
			int sid = symbolicUtil
					.getDyscopeId(pointer.getSource(), eval.value);
			state = eval.state;
			if (sid < 0) {
				errorLogger
						.logSimpleError(pointer.getSource(), state, process,
								symbolicAnalyzer.stateInformation(state),
								ErrorKind.DEREFERENCE,
								"Attempt to dereference pointer into scope which has been removed from state");
				throw new UnsatisfiablePathConditionException();
			}
			return new Evaluation(state, modelFactory.scopeValue(sid));
		case DOT:
			return evaluateScopeofExpressionWorker(state, pid, process,
					(LHSExpression) (((DotExpression) expression)
							.structOrUnion()));
		case SUBSCRIPT:
			return evaluateScopeofExpressionWorker(
					state,
					pid,
					process,
					(LHSExpression) (((SubscriptExpression) expression).array()));

		case VARIABLE:// VARIABLE
			int scopeId = state.getDyscopeID(pid,
					((VariableExpression) expression).variable());

			return new Evaluation(state, modelFactory.scopeValue(scopeId));
		default:
			throw new CIVLUnimplementedFeatureException(
					"scope of expression with operand of "
							+ expression.lhsExpressionKind() + " kind");
		}
	}

	private Evaluation evaluateShiftleft(State state, int pid,
			BinaryExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.left());
		SymbolicExpression left = eval.value, right, result;

		eval = evaluate(eval.state, pid, expression.right());
		right = eval.value;
		state = eval.state;
		result = universe.apply(this.shiftLeftFunc, Arrays.asList(left, right));
		return new Evaluation(state, result);
	}

	private Evaluation evaluateShiftright(State state, int pid,
			BinaryExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.left());
		SymbolicExpression left = eval.value, right, result;

		eval = evaluate(eval.state, pid, expression.right());
		right = eval.value;
		state = eval.state;
		result = universe
				.apply(this.shiftRightFunc, Arrays.asList(left, right));
		return new Evaluation(state, result);
	}

	/**
	 * Evaluate a struct literal expression.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The struct literal expression.
	 * @return The symbolic representation of the struct literal expression.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateStructOrUnionLiteral(State state, int pid,
			StructOrUnionLiteralExpression expression)
			throws UnsatisfiablePathConditionException {
		Expression[] fields = expression.fields();
		SymbolicType dynamicStructType = expression.getExpressionType()
				.getDynamicType(universe);
		ArrayList<SymbolicExpression> symbolicFields = new ArrayList<>();
		Evaluation eval;

		if (expression.isStruct()) {
			for (Expression field : fields) {
				eval = evaluate(state, pid, field);
				symbolicFields.add(eval.value);
				state = eval.state;
			}
			assert dynamicStructType instanceof SymbolicTupleType;
			return new Evaluation(state, universe.tuple(
					(SymbolicTupleType) dynamicStructType, symbolicFields));
		} else {
			int numberOfMembers = fields.length;
			SymbolicExpression unionValue;
			SymbolicUnionType unionType = (SymbolicUnionType) dynamicStructType;

			assert dynamicStructType instanceof SymbolicUnionType;
			eval = evaluate(state, pid, fields[numberOfMembers - 1]);
			state = eval.state;
			unionValue = universe.unionInject(unionType,
					universe.intObject(numberOfMembers - 1), eval.value);

			return new Evaluation(state, unionValue);
		}
	}

	/**
	 * Evaluate a unary expression.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The unary expression.
	 * @return The symbolic representation of the unary expression.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateUnary(State state, int pid,
			UnaryExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.operand());

		switch (expression.operator()) {
		case NEGATIVE:
			eval.value = universe.minus((NumericExpression) eval.value);
			break;
		case NOT:
			eval.value = universe.not((BooleanExpression) eval.value);
			break;
		case BIG_O:
			eval.value = universe.apply(bigOFunction,
					new Singleton<SymbolicExpression>(eval.value));
			break;
		default:
			throw new CIVLUnimplementedFeatureException(
					"evaluating unary operator " + expression.operator(),
					expression);
		}
		return eval;
	}

	/**
	 * Evaluate a variable expression.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The variable expression.
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateVariable(State state, int pid, String process,
			VariableExpression expression, boolean checkUndefinedValue)
			throws UnsatisfiablePathConditionException {
		if (expression.variable().isOutput()) {
			errorLogger.logSimpleError(expression.getSource(), state, process,
					this.symbolicAnalyzer.stateInformation(state),
					ErrorKind.OUTPUT_READ,
					"attempt to read the output variable "
							+ expression.variable().name());
			throw new UnsatisfiablePathConditionException();
		} else {
			SymbolicExpression value = state
					.valueOf(pid, expression.variable());

			if (checkUndefinedValue && value.isNull()) {
				errorLogger.logSimpleError(expression.getSource(), state,
						process, this.symbolicAnalyzer.stateInformation(state),
						ErrorKind.UNDEFINED_VALUE,
						"attempt to read uninitialized variable " + expression);
				throw new UnsatisfiablePathConditionException();
			}
			return new Evaluation(state, value);
		}
	}

	/**
	 * evaluate a system guard expression
	 * 
	 * @param state
	 *            The state where the computation happens.
	 * @param pid
	 *            The ID of the process that wants to evaluate the guard.
	 * @param expression
	 *            The system guard expression to be evaluated.
	 * @return The result of the evaluation, including the state and the
	 *         symbolic expression of the value.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateSystemGuard(State state, int pid,
			SystemGuardExpression expression)
			throws UnsatisfiablePathConditionException {
		return getSystemGuard(expression.getSource(), state, pid,
				expression.library(), expression.functionName(),
				expression.arguments());
	}

	/**
	 * Evaluates the dynamic type of a given CIVL type at a certain state. When
	 * the CIVL type has some state, e.g., an array type with a variable as the
	 * extent, the type needs to be evaluated.
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the process where the computation happens.
	 * @param type
	 *            The CIVL type to be evaluated for the dynamic type.
	 * @param source
	 *            The source code element for error report.
	 * @param isDefinition
	 *            The flag denoting if the type is a definition.
	 * @return The dynamic type of the given type.
	 * @throws UnsatisfiablePathConditionException
	 */
	private TypeEvaluation getDynamicType(State state, int pid, CIVLType type,
			CIVLSource source, boolean isDefinition)
			throws UnsatisfiablePathConditionException {
		TypeEvaluation result;

		// if type has a state variable and computeStructs is false, use
		// variable else compute
		if (type instanceof CIVLPrimitiveType) {
			result = new TypeEvaluation(state, type.getDynamicType(universe));
		} else if (type instanceof CIVLPointerType) {
			result = new TypeEvaluation(state, pointerType);
		} else if (type.getStateVariable() != null && !isDefinition) {
			SymbolicExpression value = state.valueOf(pid,
					type.getStateVariable());

			result = new TypeEvaluation(state, symbolicUtil.getType(source,
					value));
		} else if (type instanceof CIVLArrayType) {
			CIVLArrayType arrayType = (CIVLArrayType) type;
			TypeEvaluation elementTypeEval = getDynamicType(state, pid,
					arrayType.elementType(), source, false);

			if (arrayType.isComplete()) {
				Evaluation lengthEval = evaluate(elementTypeEval.state, pid,
						((CIVLCompleteArrayType) arrayType).extent());
				NumericExpression length = (NumericExpression) lengthEval.value;

				result = new TypeEvaluation(lengthEval.state,
						universe.arrayType(elementTypeEval.type, length));
			} else {
				result = new TypeEvaluation(elementTypeEval.state,
						universe.arrayType(elementTypeEval.type));
			}
		} else if (type instanceof CIVLStructOrUnionType) {
			CIVLStructOrUnionType structType = (CIVLStructOrUnionType) type;
			int numFields = structType.numFields();
			LinkedList<SymbolicType> componentTypes = new LinkedList<SymbolicType>();
			SymbolicType symbolicType;

			for (int i = 0; i < numFields; i++) {
				StructOrUnionField field = structType.getField(i);
				TypeEvaluation componentEval = getDynamicType(state, pid,
						field.type(), source, false);

				state = componentEval.state;
				componentTypes.add(componentEval.type);
			}
			if (structType.isStructType())
				symbolicType = universe.tupleType(structType.name()
						.stringObject(), componentTypes);
			else
				symbolicType = universe.unionType(structType.name()
						.stringObject(), componentTypes);
			result = new TypeEvaluation(state, symbolicType);
		} else if (type instanceof CIVLBundleType) {
			result = new TypeEvaluation(state, type.getDynamicType(universe));
		} else if (type instanceof CIVLHeapType) {
			result = new TypeEvaluation(state, this.heapType);
		} else if (type instanceof CIVLEnumType) {
			result = new TypeEvaluation(state, type.getDynamicType(universe));
		} else if (type instanceof CIVLDomainType) {
			result = new TypeEvaluation(state, type.getDynamicType(universe));
		} else if (type instanceof CIVLFunctionType) {
			result = new TypeEvaluation(state, type.getDynamicType(universe));
		} else
			throw new CIVLInternalException("Unreachable", source);
		return result;
	}

	private Evaluation getSystemGuard(CIVLSource source, State state, int pid,
			String library, String function, List<Expression> arguments)
			throws UnsatisfiablePathConditionException {
		try {
			LibraryEvaluator libEvaluator = this.libLoader.getLibraryEvaluator(
					library, this, this.modelFactory, symbolicUtil,
					symbolicAnalyzer);
			Expression[] args = new Expression[arguments.size()];

			arguments.toArray(args);
			return libEvaluator.evaluateGuard(source, state, pid, function,
					args);
		} catch (LibraryLoaderException exception) {
			String process = state.getProcessState(pid).name() + "(id=" + pid
					+ ")";
			StringBuffer message = new StringBuffer();
			int numArgs = arguments.size();
			SymbolicExpression[] argumentValues = new SymbolicExpression[numArgs];

			for (int i = 0; i < numArgs; i++) {
				Evaluation eval = this.evaluate(state, pid, arguments.get(i));

				state = eval.state;
				argumentValues[i] = eval.value;
			}
			message.append("unable to load the library evaluator for the library ");
			message.append(library);
			message.append(" for the function ");
			message.append(function);
			this.errorLogger.logSimpleError(source, state, process,
					this.symbolicAnalyzer.stateInformation(state),
					ErrorKind.LIBRARY, message.toString());
			return new Evaluation(state,
					this.symbolicUtil.getAbstractGuardOfFunctionCall(library,
							function, argumentValues));
		}
	}

	// private Set<SymbolicExpression> heapCells(State state, int dyscopeId) {
	// SymbolicExpression heapValue = state.getVariableValue(dyscopeId, 0);
	//
	// if (heapValue.isNull())
	// return new HashSet<>();
	// else {
	// CIVLHeapType heapType = modelFactory.heapType();
	// int numMallocs = heapType.getNumMallocs();
	// Set<SymbolicExpression> result = new HashSet<>();
	//
	// for (int i = 0; i < numMallocs; i++) {
	// ReferenceExpression ref = universe.tupleComponentReference(
	// identityReference, universe.intObject(i));
	// SymbolicExpression heapCell = symbolicUtil.makePointer(
	// dyscopeId, 0, ref);
	//
	// result.add(heapCell);
	// }
	// return result;
	// }
	// }

	// TODO: add doc here
	private Evaluation initialValueOfType(State state, int pid, CIVLType type)
			throws UnsatisfiablePathConditionException {
		TypeKind kind = type.typeKind();
		Evaluation eval = null;

		switch (kind) {
		case ARRAY: {
			CIVLArrayType arrayType = (CIVLArrayType) type;
			CIVLType elementType = arrayType.elementType();

			eval = new Evaluation(state, universe.emptyArray(elementType
					.getDynamicType(universe)));
			break;
		}
		case COMPLETE_ARRAY: {
			CIVLCompleteArrayType arrayType = (CIVLCompleteArrayType) type;
			CIVLType elementType = arrayType.elementType();
			SymbolicExpression elementValue;
			NumericExpression extent;

			eval = initialValueOfType(state, pid, elementType);
			state = eval.state;
			elementValue = eval.value;
			eval = this.evaluate(state, pid, arrayType.extent());
			state = eval.state;
			extent = (NumericExpression) eval.value;
			eval.value = symbolicUtil.newArray(state.getPathCondition(),
					elementType.getDynamicType(universe), extent, elementValue);
			break;
		}
		case BUNDLE:
			eval = new Evaluation(state, universe.nullExpression());
			break;
		case DOMAIN: {
			CIVLDomainType domainType = (CIVLDomainType) type;
			SymbolicExpression initDomainValue;
			int dim;
			SymbolicType integerType = universe.integerType();
			SymbolicTupleType tupleType = universe.tupleType(universe
					.stringObject("domain"), Arrays.asList(integerType,
					integerType,
					universe.arrayType(universe.arrayType(integerType))));
			List<SymbolicExpression> tupleComponents = new LinkedList<>();

			tupleComponents.add(one);
			tupleComponents.add(one);
			tupleComponents.add(universe.emptyArray(universe
					.arrayType(integerType)));
			if (domainType.isComplete()) {
				CIVLCompleteDomainType compDomainType = (CIVLCompleteDomainType) domainType;

				dim = compDomainType.getDimension();
				tupleComponents.set(0, universe.integer(dim));

			}
			initDomainValue = universe.tuple(tupleType, tupleComponents);
			eval = new Evaluation(state, initDomainValue);
			break;
		}
		case ENUM: {
			CIVLEnumType enumType = (CIVLEnumType) type;

			eval = new Evaluation(state,
					universe.integer(enumType.firstValue()));
			break;
		}
		case POINTER:
			eval = new Evaluation(state, symbolicUtil.nullPointer());
			break;
		case PRIMITIVE: {
			CIVLPrimitiveType primitiveType = (CIVLPrimitiveType) type;

			eval = new Evaluation(state, primitiveType.initialValue(universe));
			break;
		}
		default:// STRUCT_OR_UNION{ // TODO: don't make this the default!
		{
			CIVLStructOrUnionType strOrUnion = (CIVLStructOrUnionType) type;

			if (strOrUnion.isUnionType()) {
				eval = this.initialValueOfType(state, pid,
						strOrUnion.getField(0).type());
				eval.value = universe
						.unionInject((SymbolicUnionType) strOrUnion
								.getDynamicType(universe), this.zeroObj,
								eval.value);
			} else {
				int size = strOrUnion.numFields();
				List<SymbolicExpression> components = new ArrayList<>(size);

				for (int i = 0; i < size; i++) {
					eval = this.initialValueOfType(state, pid, strOrUnion
							.getField(i).type());
					state = eval.state;
					components.add(eval.value);
				}
				eval = new Evaluation(state,
						universe.tuple((SymbolicTupleType) strOrUnion
								.getDynamicType(universe), components));
			}
		}
		}
		return eval;
	}

	/**
	 * Checks if a value of type scope, process, or pointer type is defined. If
	 * the value of those types is undefined (e.g., process -1, scope -1,
	 * pointer<-1, ..., ...>), an error should be reported.
	 * 
	 * @param state
	 *            The state where the checking happens.
	 * @param expression
	 *            The static representation of the value.
	 * @param expressionValue
	 *            The symbolic value to be checked if it is defined.
	 * @throws UnsatisfiablePathConditionException
	 */
	private void isValueDefined(State state, String process,
			Expression expression, SymbolicExpression expressionValue)
			throws UnsatisfiablePathConditionException {
		CIVLSource source = expression.getSource();
		CIVLType expressionType = expression.getExpressionType();

		if (expressionType.equals(typeFactory.scopeType())) {
			if (expressionValue.equals(modelFactory.undefinedValue(typeFactory
					.scopeSymbolicType()))) {
				errorLogger.logSimpleError(source, state, process,
						symbolicAnalyzer.stateInformation(state),
						ErrorKind.UNDEFINED_VALUE,
						"Attempt to evaluate an invalid scope reference");
				throw new UnsatisfiablePathConditionException();
			}
		} else if (expressionType.equals(typeFactory.processType())) {
			if (expressionValue.equals(modelFactory.undefinedValue(typeFactory
					.processSymbolicType()))) {
				errorLogger.logSimpleError(source, state, process,
						symbolicAnalyzer.stateInformation(state),
						ErrorKind.UNDEFINED_VALUE,
						"Attempt to evaluate an invalid process reference");
				throw new UnsatisfiablePathConditionException();
			}
		} else if (expressionValue.type().equals(this.pointerType)) {
			if (this.civlConfig.svcomp()) {
				if (expressionValue.operator() != SymbolicOperator.CONCRETE)
					return;
			}
			if (this.symbolicUtil.isNullPointer(expressionValue))
				return;
			if (this.symbolicUtil.applyReverseFunction(INT_TO_POINTER_FUNCTION,
					expressionValue) != null)
				return;
			try {
				int scopeID = symbolicUtil
						.getDyscopeId(source, expressionValue);

				if (scopeID < 0) {
					StringBuffer message = new StringBuffer();

					message.append("Attempt to evaluate a pointer refererring to memory of an invalid scope:\n");
					message.append("pointer expression: "
							+ expression.toString() + "\n");
					message.append("value: " + expressionValue);
					errorLogger.logSimpleError(source, state, process,
							symbolicAnalyzer.stateInformation(state),
							ErrorKind.MEMORY_LEAK, message.toString());
					throw new UnsatisfiablePathConditionException();
				}
			} catch (Exception e) {
				errorLogger.logSimpleError(source, state, process,
						symbolicAnalyzer.stateInformation(state),
						ErrorKind.UNDEFINED_VALUE,
						"Attempt to use undefined pointer");
				throw new UnsatisfiablePathConditionException();
			}
		}
	}

	/**
	 * zero
	 * 
	 * @param source
	 * @param type
	 * @return
	 */
	private NumericExpression zeroOf(CIVLSource source, CIVLType type) {
		if (type instanceof CIVLPrimitiveType) {
			if (((CIVLPrimitiveType) type).primitiveTypeKind() == PrimitiveTypeKind.INT)
				return zero;
			if (((CIVLPrimitiveType) type).primitiveTypeKind() == PrimitiveTypeKind.REAL)
				return zeroR;
		}
		throw new CIVLInternalException("Expected integer or real type, not "
				+ type, source);
	}

	/* ********************* Pointer addition helpers ************************ */
	/**
	 * This is a Helper function for
	 * {@link Evaluator#pointerAdd(State, int, String, BinaryExpression, SymbolicExpression, NumericExpression)}
	 * . <br>
	 * It returns:<br>
	 * The {@link Evaluation} object wraps the new pointer after adding an
	 * increment or decrement.<br>
	 * 
	 * The {@link ArrayList} of {@link NumericExpression} is an appendix of the
	 * returned objects which is aiming to reduce redundant computation. It
	 * stores the dimension information for each dimension of the array pointed
	 * by the input pointer. NOTE: the appendix will be returned only if it's
	 * computed during the execution of this function, otherwise it null.
	 * 
	 * @param state
	 *            The current state
	 * @param process
	 *            The String identifier of the process
	 * @param pointer
	 *            The {@link SymbolicExpression} of the original pointer before
	 *            addition
	 * @param offset
	 *            The {@link NumericExpression} of the offset will be added on
	 *            the pointer
	 * @param checkOutput
	 *            Dereferencing operation has to check if the object pointed by
	 *            input pointer is an output variable if this flag is set TRUE
	 * @param source
	 *            {@link CIVLSource} of the pointer addition statement
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 * 
	 * @author ziqing
	 */
	private Pair<Evaluation, NumericExpression[]> pointerAddWorker(State state,
			String process, SymbolicExpression pointer,
			NumericExpression offset, boolean checkOutput, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression arrayPtr;
		ReferenceExpression parentRef;
		NumericExpression extent, index;
		ReferenceExpression ref;
		ReferenceExpression newRef;
		BooleanExpression claim, notEqual;
		BooleanExpression notOver;// pred:ptr add doesn't beyond bound
		BooleanExpression notDrown;// pred:ptr add doesn't lower than bound
		BooleanExpression outCondExpr;
		Evaluation eval;
		int scopeId, vid;
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		ResultType resultType = null;
		boolean isOutBound = false;

		claim = universe.equals(offset, zero);
		if (reasoner.isValid(claim))
			return new Pair<>(new Evaluation(state, pointer), null);
		scopeId = symbolicUtil.getDyscopeId(source, pointer);
		vid = symbolicUtil.getVariableId(source, pointer);
		ref = symbolicUtil.getSymRef(pointer);
		// Checking if the pointer addition will be out of bound at the current
		// dimension.
		assert ref.isArrayElementReference();

		arrayPtr = symbolicUtil.parentPointer(source, pointer);
		index = ((ArrayElementReference) ref).getIndex();
		eval = dereference(source, state, process, null, arrayPtr, false);
		state = eval.state;
		if (!(eval.value.type() instanceof SymbolicCompleteArrayType)) {
			errorLogger
					.logSimpleError(source, state, process,
							symbolicAnalyzer.stateToString(state),
							ErrorKind.POINTER,
							"Pointer addition on an element reference on an incomplete array");
			return new Pair<>(new Evaluation(state, symbolicUtil.makePointer(
					pointer, universe.offsetReference(ref, offset))), null);
		}
		extent = ((SymbolicCompleteArrayType) eval.value.type()).extent();
		// Not beyond the bound
		notOver = universe.lessThanEquals(universe.add(index, offset), extent);
		// Not lower than the bound
		notDrown = universe.lessThanEquals(zero, universe.add(index, offset));
		// Not exactly equal to the extent
		notEqual = universe.neq(universe.add(index, offset), extent);
		// Conditions of out of bound:
		// If index + offset > extent, out of bound.
		// If index + offset < 0, out of bound.
		// If index + offset == extent and the parent reference is an array
		// element reference, out of bound.(e.g. int a[2], b[2][2]. &a[2] is
		// a valid pointer, &b[0][2] should be cast to &b[1][0] unless it's
		// a sequence of memory space)
		isOutBound = true;
		outCondExpr = notOver;
		if (!this.civlConfig.svcomp()) {
			resultType = reasoner.valid(notOver).getResultType();
			if (resultType.equals(ResultType.YES)) {
				// not over
				outCondExpr = notDrown;
				resultType = reasoner.valid(notDrown).getResultType();
				if (resultType.equals(ResultType.YES)) {
					// not drown
					outCondExpr = notEqual;
					resultType = reasoner.valid(notEqual).getResultType();
					if (resultType.equals(ResultType.YES)) // not equal
						isOutBound = false;
					else if (!symbolicUtil.getSymRef(arrayPtr)
							.isArrayElementReference() || vid == 0)
						isOutBound = false; // equal but valid
				}
			}
		} else
			isOutBound = false;
		if (isOutBound) {
			// Checking if the array is an allocated memory space
			if (vid == 0)
				state = this.reportPtrAddOutOfBoundError(source, state,
						process, outCondExpr, resultType, eval.value, pointer,
						offset, false);
			return recomputeArrayIndices(state, process, vid, scopeId, pointer,
					offset, reasoner, source);
		} else {
			// The (offset + index) < extent at the given dimension,
			// return new pointer easily.
			parentRef = symbolicUtil.getSymRef(arrayPtr);
			newRef = universe.arrayElementReference(parentRef,
					universe.add(index, offset));
			eval = new Evaluation(state, symbolicUtil.makePointer(scopeId, vid,
					newRef));
			return new Pair<>(eval, null);
		}
	}

	/* ********************** Methods from Evaluator *********************** */

	@Override
	public Evaluation evaluate(State state, int pid, Expression expression,
			boolean checkUndefinedValue)
			throws UnsatisfiablePathConditionException {
		ExpressionKind kind = expression.expressionKind();
		Evaluation result;
		int processIdentifier = state.getProcessState(pid).identifier();
		String process = "p" + processIdentifier + " (id = " + pid + ")";

		if (expression.hasConstantValue())
			return new Evaluation(state, expression.constantValue());
		switch (kind) {
		case ABSTRACT_FUNCTION_CALL:
			result = evaluateAbstractFunctionCall(state, pid,
					(AbstractFunctionCallExpression) expression);
			break;
		case ADDRESS_OF:
			result = evaluateAddressOf(state, pid,
					(AddressOfExpression) expression);
			break;
		case ARRAY_LITERAL:
			result = evaluateArrayLiteral(state, pid,
					(ArrayLiteralExpression) expression);
			break;
		case BINARY:
			result = evaluateBinary(state, pid, process,
					(BinaryExpression) expression);
			break;
		case BOOLEAN_LITERAL:
			result = evaluateBooleanLiteral(state, pid,
					(BooleanLiteralExpression) expression);
			break;
		case BOUND_VARIABLE:
			result = evaluateBoundVariable(state, pid,
					(BoundVariableExpression) expression);
			break;
		case CAST:
			result = evaluateCast(state, pid, process,
					(CastExpression) expression);
			break;
		case CHAR_LITERAL:
			result = evaluateCharLiteral(state, pid,
					(CharLiteralExpression) expression);
			break;
		case COND:
			throw new CIVLInternalException("Conditional expressions should "
					+ "be translated away by CIVL model builder ",
					expression.getSource());
		case DEREFERENCE:
			result = evaluateDereference(state, pid, process,
					(DereferenceExpression) expression);
			break;
		case DERIVATIVE:
			result = evaluateDerivativeCall(state, pid,
					(DerivativeCallExpression) expression);
			break;
		case DOMAIN_GUARD:
			result = evaluateDomainGuard(state, pid,
					(DomainGuardExpression) expression);
			break;
		case REC_DOMAIN_LITERAL:
			result = evaluateRecDomainLiteral(state, pid,
					(RecDomainLiteralExpression) expression);
			break;
		case DOT:
			result = evaluateDot(state, pid, process,
					(DotExpression) expression);
			break;
		case DYNAMIC_TYPE_OF:
			result = evaluateDynamicTypeOf(state, pid,
					(DynamicTypeOfExpression) expression);
			break;
		case FUNCTION_IDENTIFIER:
			result = evaluateFunctionIdentifierExpression(state, pid,
					(FunctionIdentifierExpression) expression);
			break;
		case FUNCTION_GUARD:
			result = evaluateFunctionGuard(state, pid, process,
					(FunctionGuardExpression) expression);
			break;
		case HERE_OR_ROOT:
			result = evaluateHereOrRootScope(state, pid,
					(HereOrRootExpression) expression);
			break;
		case INITIAL_VALUE:
			result = evaluateInitialValue(state, pid,
					(InitialValueExpression) expression);
			break;
		case INTEGER_LITERAL:
			result = evaluateIntegerLiteral(state, pid,
					(IntegerLiteralExpression) expression);
			break;
		case REAL_LITERAL:
			result = evaluateRealLiteral(state, pid,
					(RealLiteralExpression) expression);
			break;
		case REGULAR_RANGE:
			result = evaluateRegularRange(state, pid,
					(RegularRangeExpression) expression);
			break;
		case SCOPEOF:
			result = evaluateScopeofExpression(state, pid, process,
					(ScopeofExpression) expression);
			break;
		case SELF:
			result = evaluateSelf(state, pid, (SelfExpression) expression);
			break;
		case PROC_NULL:
			result = this.evaluateProcnull(state, pid,
					(ProcnullExpression) expression);
			break;
		case SIZEOF_TYPE:
			result = evaluateSizeofTypeExpression(state, pid,
					(SizeofTypeExpression) expression);
			break;
		case SIZEOF_EXPRESSION:
			result = evaluateSizeofExpressionExpression(state, pid,
					(SizeofExpression) expression);
			break;
		case STRUCT_OR_UNION_LITERAL:
			result = evaluateStructOrUnionLiteral(state, pid,
					(StructOrUnionLiteralExpression) expression);
			break;
		case SUBSCRIPT:
			result = evaluateSubscript(state, pid, process,
					(SubscriptExpression) expression);
			break;
		case SYSTEM_GUARD:
			result = evaluateSystemGuard(state, pid,
					(SystemGuardExpression) expression);
			break;
		case UNARY:
			result = evaluateUnary(state, pid, (UnaryExpression) expression);
			break;
		case UNDEFINED_PROC:
			result = new Evaluation(state,
					modelFactory.undefinedValue(typeFactory
							.processSymbolicType()));
			break;
		case VARIABLE:
			result = evaluateVariable(state, pid, process,
					(VariableExpression) expression, checkUndefinedValue);
			break;
		case QUANTIFIER:
			result = evaluateQuantifiedExpression(state, pid,
					(QuantifiedExpression) expression);
			break;
		case SYSTEM_FUNC_CALL:
		case MEMORY_UNIT:
		case NULL_LITERAL:
		case STRING_LITERAL:
			throw new CIVLSyntaxException("Illegal use of " + kind
					+ " expression: ", expression.getSource());
		default:
			throw new CIVLInternalException("unreachable", expression);
		}
		return result;
	}

	@Override
	public Evaluation evaluateSizeofType(CIVLSource source, State state,
			int pid, CIVLType type) throws UnsatisfiablePathConditionException {
		Evaluation eval;

		if (type instanceof CIVLPrimitiveType) {
			NumericExpression value = ((CIVLPrimitiveType) type).getSizeof();
			BooleanExpression facts = ((CIVLPrimitiveType) type).getFacts();
			BooleanExpression pathCondition = universe.and(facts,
					state.getPathCondition());

			state = state.setPathCondition(pathCondition);
			eval = new Evaluation(state, value);
		} else if (type instanceof CIVLCompleteArrayType) {
			NumericExpression extentValue;

			eval = evaluate(state, pid, ((CIVLCompleteArrayType) type).extent());
			extentValue = (NumericExpression) eval.value;
			eval = evaluateSizeofType(source, eval.state, pid,
					((CIVLArrayType) type).elementType());
			eval.value = universe.multiply(extentValue,
					(NumericExpression) eval.value);
		} else if (type instanceof CIVLArrayType) {
			throw new CIVLInternalException(
					"sizeof applied to incomplete array type", source);
		} else {
			NumericExpression sizeof;
			BooleanExpression pathCondition;

			eval = dynamicTypeOf(state, pid, type, source, false);
			sizeof = (NumericExpression) universe.apply(sizeofFunction,
					new Singleton<SymbolicExpression>(eval.value));
			pathCondition = universe.and(eval.state.getPathCondition(),
					universe.lessThan(zero, sizeof));
			eval.value = sizeof;
			eval.state = state.setPathCondition(pathCondition);
		}
		return eval;
	}

	@Override
	public Triple<State, CIVLFunction, Integer> evaluateFunctionIdentifier(
			State state, int pid, Expression functionIdentifier,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		CIVLFunction function;
		Evaluation eval = this.evaluate(state, pid, functionIdentifier);
		int scopeId = symbolicUtil.getDyscopeId(source, eval.value);
		int fid = symbolicUtil.getVariableId(source, eval.value);
		// String funcName = "";
		Scope containingScope;

		if (scopeId < 0) {
			ProcessState procState = state.getProcessState(pid);

			errorLogger.logSimpleError(source, state, procState.name() + "(id="
					+ pid + ")", symbolicAnalyzer.stateInformation(state),
					ErrorKind.MEMORY_LEAK, "invalid function pointer: "
							+ functionIdentifier);
			throw new UnsatisfiablePathConditionException();
		}
		state = eval.state;
		containingScope = state.getDyscope(scopeId).lexicalScope();
		function = containingScope.getFunction(fid);
		return new Triple<>(state, function, scopeId);
	}

	@Override
	public CIVLErrorLogger errorLogger() {
		return this.errorLogger;
	}

	@Override
	public Evaluation dereference(CIVLSource source, State state,
			String process, Expression pointerExpr, SymbolicExpression pointer,
			boolean checkOutput) throws UnsatisfiablePathConditionException {
		return dereference(source, state, process, pointerExpr, pointer,
				checkOutput, false);
	}

	/**
	 * * Only three types (represented differently in CIVL) of the symbolic
	 * expression "charPointer" is acceptable:<br>
	 * A pointer to char <br>
	 * A pointer to an element of array of char. (e.g. char a[N][M]; a[x] or
	 * &a[x][0] are acceptable. Address of an element of array of char or
	 * pointer to an array of char are same as this situation.)<br>
	 * A complete char array
	 * 
	 * @param source
	 *            The CIVL source of the pointer to char expression
	 * @param state
	 *            The current state
	 * @param process
	 *            The identifier of the process
	 * @param charPointer
	 *            The pointer to char
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	@Override
	public Triple<State, StringBuffer, Boolean> getString(CIVLSource source,
			State state, String process, Expression charPointerExpr,
			SymbolicExpression charPointer)
			throws UnsatisfiablePathConditionException {
		if (charPointer.operator() == SymbolicOperator.CONCRETE) {
			SymbolicSequence<?> originalArray = null;
			int int_arrayIndex = -1;
			StringBuffer result = new StringBuffer();
			ReferenceExpression ref = null;
			Evaluation eval;

			if (charPointer.type() instanceof SymbolicCompleteArrayType) {
				originalArray = (SymbolicSequence<?>) charPointer.argument(0);
				int_arrayIndex = 0;
			} else {
				ref = symbolicUtil.getSymRef(charPointer);
				if (ref instanceof ArrayElementReference) {
					SymbolicExpression pointerCharArray = symbolicUtil
							.parentPointer(source, charPointer);
					SymbolicExpression charArray;

					eval = dereference(source, state, process, null,
							pointerCharArray, false);
					state = eval.state;
					charArray = eval.value;
					try {
						originalArray = (SymbolicSequence<?>) charArray
								.argument(0);
					} catch (ClassCastException e) {
						// throw new CIVLUnimplementedFeatureException(
						// "non-concrete strings", source);
						return new Triple<>(state,
								charArray.toStringBuffer(true), false);
					} catch (ArrayIndexOutOfBoundsException e) {
						errorLogger.logSimpleError(source, state, process,
								symbolicAnalyzer.stateInformation(state),
								ErrorKind.UNDEFINED_VALUE,
								"reading undefined or uninitialized value from some pointer to heap: "
										+ charArray.argument(0));
						throw new UnsatisfiablePathConditionException();
					}
					int_arrayIndex = symbolicUtil.extractInt(source,
							((ArrayElementReference) ref).getIndex());

				} else {
					eval = dereference(source, state, process, charPointerExpr,
							charPointer, false);
					state = eval.state;
					// A single character is not acceptable.
					if (eval.value.arguments().length <= 1) {
						this.errorLogger.logSimpleError(source, state, process,
								this.symbolicAnalyzer.stateInformation(state),
								ErrorKind.OTHER,
								"Try to obtain a string from a sequence of char has length"
										+ " less than or equal to one");
						throw new UnsatisfiablePathConditionException();
					} else {
						originalArray = (SymbolicSequence<?>) eval.value
								.argument(0);
						int_arrayIndex = 0;
					}
				}
			}
			result = symbolicUtil.charArrayToString(source, originalArray,
					int_arrayIndex, false);
			return new Triple<>(state, result, true);
		} else
			throw new CIVLUnimplementedFeatureException("non-concrete strings",
					source);
	}

	@Override
	public Evaluation getStringExpression(State state, String process,
			CIVLSource source, SymbolicExpression charPointer)
			throws UnsatisfiablePathConditionException {
		BooleanExpression pc = state.getPathCondition();
		Reasoner reasoner = universe.reasoner(pc);
		ReferenceExpression symRef = symbolicUtil.getSymRef(charPointer);

		if (symRef.isArrayElementReference()) {
			ArrayElementReference arrayEltRef = (ArrayElementReference) symRef;
			SymbolicExpression arrayReference = symbolicUtil.parentPointer(
					source, charPointer);
			NumericExpression indexExpr = arrayEltRef.getIndex();
			Evaluation eval = this.dereference(source, state, process, null,
					arrayReference, false);
			int index;

			if (indexExpr.isZero())
				index = 0;
			else {
				IntegerNumber indexNum = (IntegerNumber) reasoner
						.extractNumber(indexExpr);

				if (indexNum == null)
					throw new CIVLUnimplementedFeatureException(
							"non-concrete symbolic index into string", source);
				index = indexNum.intValue();
			}
			if (index == 0)
				return eval;
			else if (index > 0) {
				SymbolicExpression arrayValue = eval.value;
				SymbolicArrayType arrayType = (SymbolicArrayType) arrayValue
						.type();
				LinkedList<SymbolicExpression> charExprList = new LinkedList<>();
				int length;

				if (arrayType.isComplete()) {
					NumericExpression extent = ((SymbolicCompleteArrayType) arrayType)
							.extent();
					IntegerNumber extentNum = (IntegerNumber) reasoner
							.extractNumber(extent);

					if (extentNum == null)
						throw new CIVLUnimplementedFeatureException(
								"pointer into string of non-concrete length",
								source);
					length = extentNum.intValue();
				} else
					throw new CIVLUnimplementedFeatureException(
							"pointer into string of unknown length", source);
				for (int i = index; i < length; i++) {
					SymbolicExpression charExpr = universe.arrayRead(
							arrayValue, universe.integer(i));

					charExprList.add(charExpr);
					// if you wanted to get heavy-weight, call the prover to see
					// if charExpr equals the null character instead of this:
					if (nullCharExpr.equals(charExpr))
						break;
				}
				eval.value = universe.array(charType, charExprList);
				return eval;
			} else
				throw new CIVLInternalException("negative pointer index: "
						+ index, source);
		}
		throw new CIVLUnimplementedFeatureException(
				"pointer to char is not into an array of char", source);
	}

	@Override
	public ModelFactory modelFactory() {
		return modelFactory;
	}

	@Override
	public Evaluation pointerAdd(State state, int pid, String process,
			BinaryExpression expression, SymbolicExpression pointer,
			NumericExpression offset)
			throws UnsatisfiablePathConditionException {
		if (!symbolicUtil.isDefinedPointer(pointer)) {
			errorLogger
					.logSimpleError(expression.getSource(), state, process,
							symbolicAnalyzer.stateInformation(state),
							ErrorKind.DEREFERENCE,
							"Attempt to performs pointer addition upon an undefined pointer");
			throw new UnsatisfiablePathConditionException();
		} else {
			ReferenceExpression symRef = symbolicUtil.getSymRef(pointer);

			if (symRef.isArrayElementReference()) {
				return (this.pointerAddWorker(state, process, pointer, offset,
						false, expression.left().getSource())).left;
			} else if (symRef.isOffsetReference()) {
				OffsetReference offsetRef = (OffsetReference) symRef;
				NumericExpression oldOffset = offsetRef.getOffset();
				NumericExpression newOffset = universe.add(oldOffset, offset);
				Evaluation eval;

				if (!this.civlConfig.svcomp()) {
					// TODO change to andTo
					BooleanExpression claim = universe.and(
							universe.lessThanEquals(zero, newOffset),
							universe.lessThanEquals(newOffset, one));
					BooleanExpression assumption = state.getPathCondition();
					ResultType resultType = universe.reasoner(assumption)
							.valid(claim).getResultType();

					if (resultType != ResultType.YES) {
						state = errorLogger
								.logError(expression.getSource(), state,
										process, symbolicAnalyzer
												.stateInformation(state),
										claim, resultType,
										ErrorKind.OUT_OF_BOUNDS,
										"Pointer addition resulted in out of bounds.\nobject pointer:"
												+ pointer + "\n" + "offset = "
												+ offset);
						// recovered, invalid pointer cannot be dereferenced,
						// but execution is not suppose to stop here:
					}
				}
				eval = new Evaluation(state, symbolicUtil.setSymRef(pointer,
						universe.offsetReference(offsetRef.getParent(),
								newOffset)));
				return eval;
			} else if (symRef.isIdentityReference()) {
				BooleanExpression claim;
				BooleanExpression assumption;
				ResultType resultType;

				claim = universe.equals(zero, offset);
				assumption = state.getPathCondition();
				resultType = universe.reasoner(assumption).valid(claim)
						.getResultType();
				if (resultType.equals(ResultType.YES))
					return new Evaluation(state, pointer);
				claim = universe.equals(one, offset);
				assumption = state.getPathCondition();
				resultType = universe.reasoner(assumption).valid(claim)
						.getResultType();
				if (resultType.equals(ResultType.YES))
					return new Evaluation(state, symbolicUtil.makePointer(
							pointer, universe.offsetReference(symRef, one)));
				else {
					state = errorLogger.logError(expression.getSource(), state,
							process, symbolicAnalyzer.stateInformation(state),
							claim, resultType, ErrorKind.OUT_OF_BOUNDS,
							"Pointer addition resulted in out of bounds.\nobject pointer:"
									+ pointer + "\noffset = " + offset);
					// recovered, invalid pointer cannot be dereferenced, but
					// execution is not suppose to stop here:
					return new Evaluation(state, symbolicUtil.makePointer(
							pointer, universe.offsetReference(symRef, offset)));
				}
			} else
				throw new CIVLUnimplementedFeatureException(
						"Pointer addition for anything other than array elements or variables",
						expression);
		}
	}

	@Override
	public Evaluation pointerSubtraction(State state, int pid, String process,
			BinaryExpression expression, SymbolicExpression leftPtr,
			SymbolicExpression rightPtr)
			throws UnsatisfiablePathConditionException {
		int leftVid, leftSid, rightVid, rightSid;
		SymbolicExpression array, arrayPtr;
		NumericExpression leftPos = zero, rightPos = zero;
		NumericExpression[] leftPtrIndices, rightPtrIndices;
		NumericExpression[] arraySliceSizes;
		Evaluation eval;

		// ModelFactory already checked type compatibility, so here we just
		// check if these two pointers are pointing to same object and array
		// element reference pointers.
		leftVid = symbolicUtil.getVariableId(expression.left().getSource(),
				leftPtr);
		leftSid = symbolicUtil.getDyscopeId(expression.left().getSource(),
				leftPtr);
		rightVid = symbolicUtil.getVariableId(expression.right().getSource(),
				rightPtr);
		rightSid = symbolicUtil.getDyscopeId(expression.right().getSource(),
				rightPtr);

		if (rightSid == -1 && rightVid == -1) {
			// offset subtraction
			return new Evaluation(state,
					this.symbolicAnalyzer.pointerArithmetics(
							expression.getSource(), state, true, leftPtr,
							rightPtr));
		} else {
			// Check if the two point to the same object
			if ((rightVid != leftVid) || (rightSid != leftSid)) {
				state = errorLogger.logError(expression.getSource(), state,
						process, symbolicAnalyzer.stateInformation(state),
						null, ResultType.NO, ErrorKind.POINTER,
						"Operands of pointer subtraction don't point to the "
								+ "same obejct");
				throw new UnsatisfiablePathConditionException();
			}
			// Check if two pointers are array element reference pointers. Based
			// on
			// C11 Standard 6.5.6, entry 9: When two pointers are subtracted,
			// both
			// shall point to elements of the same array object, or one past the
			// last element of the array object; the result is the difference of
			// the
			// subscripts of the two array elements.
			// Thus, any pointer which is not an array element reference is
			// invalid
			// for pointer subtraction.
			if (!(symbolicUtil.getSymRef(leftPtr).isArrayElementReference() && symbolicUtil
					.getSymRef(rightPtr).isArrayElementReference()))
				state = errorLogger
						.logError(expression.getSource(), state, process,
								symbolicAnalyzer.stateInformation(state), null,
								ResultType.NO, ErrorKind.POINTER,
								"Not both of the operands of pointer subtraction points to an array element");
			// Get the pointer to the whole array
			arrayPtr = symbolicUtil.arrayRootPtr(leftPtr, expression.left()
					.getSource());
			leftPtrIndices = symbolicUtil
					.stripIndicesFromReference((ArrayElementReference) symbolicUtil
							.getSymRef(leftPtr));
			rightPtrIndices = symbolicUtil
					.stripIndicesFromReference((ArrayElementReference) symbolicUtil
							.getSymRef(rightPtr));
			// Check compatibility for heap objects:
			// If VID == 0, all ancestor indexes of left pointer should be same
			// as
			// right pointer. Because different heap objects all have variable
			// ID of
			// number zero and ancestor indexes indicate if they are same heap
			// objects.
			if (leftVid == 0) {
				boolean isCompatiable = true;
				int temp = leftPtrIndices.length - 1;

				if (leftPtrIndices.length != rightPtrIndices.length)
					isCompatiable = false;
				else {

					for (int i = 0; i < temp; i++) {
						if (!(leftPtrIndices[i].equals(rightPtrIndices[i]))) {
							isCompatiable = false;
							break;
						}
					}
				}
				if (!isCompatiable)
					state = errorLogger
							.logError(expression.getSource(), state, process,
									symbolicAnalyzer.stateInformation(state),
									null, ResultType.NO, ErrorKind.POINTER,
									"Operands of pointer subtraction point to different heap obejcts");
				// Since they are in the same heap object, the result is
				// directly
				// do a subtraction between two indexes
				eval = new Evaluation(state, null);
				eval.value = universe.subtract(leftPtrIndices[temp],
						rightPtrIndices[temp]);
				return eval;
			}
			// Get array by dereferencing array pointer
			eval = this.dereference(expression.left().getSource(), state,
					process, null, arrayPtr, false);
			state = eval.state;
			array = eval.value;
			arraySliceSizes = symbolicUtil.arraySlicesSizes(symbolicUtil
					.arrayCoordinateSizes((SymbolicCompleteArrayType) array
							.type()));
			for (int i = leftPtrIndices.length, j = arraySliceSizes.length - 1; --i >= 0; j--) {
				NumericExpression leftIdx, rightIdx;
				NumericExpression sliceSizes = arraySliceSizes[j];

				leftIdx = leftPtrIndices[i];
				rightIdx = rightPtrIndices[i];
				leftPos = universe.add(leftPos,
						universe.multiply(leftIdx, sliceSizes));
				rightPos = universe.add(rightPos,
						universe.multiply(rightIdx, sliceSizes));
			}
			eval.state = state;
			eval.value = universe.subtract(leftPos, rightPos);
			return eval;
		}
	}

	@Override
	public Evaluation reference(State state, int pid, LHSExpression operand)
			throws UnsatisfiablePathConditionException {
		Evaluation result;

		if (operand instanceof VariableExpression) {
			Variable variable = ((VariableExpression) operand).variable();
			int sid = state.getDyscopeID(pid, variable);
			int vid = variable.vid();

			result = new Evaluation(state, symbolicUtil.makePointer(sid, vid,
					identityReference));
		} else if (operand instanceof SubscriptExpression) {
			LHSExpression arrayExpr = ((SubscriptExpression) operand).array();
			Evaluation refEval = reference(state, pid, arrayExpr);
			SymbolicExpression arrayPointer = refEval.value;
			ReferenceExpression oldSymRef = symbolicUtil
					.getSymRef(arrayPointer);
			NumericExpression index;
			ReferenceExpression newSymRef;
			SymbolicExpression array;
			SymbolicArrayType arrayType;

			result = evaluate(refEval.state, pid,
					((SubscriptExpression) operand).index());
			index = (NumericExpression) result.value;
			result = this.dereference(operand.getSource(), state, state
					.getProcessState(pid).name(), operand, arrayPointer, false);
			array = result.value;
			arrayType = (SymbolicArrayType) array.type();
			if (array.type() == null)
				arrayType = (SymbolicArrayType) arrayExpr.getExpressionType()
						.getDynamicType(universe);
			result.state = this.checkArrayIndexInBound(state,
					operand.getSource(), state.getProcessState(pid).name(),
					arrayType, array, index, true);
			newSymRef = universe.arrayElementReference(oldSymRef, index);
			result.value = symbolicUtil.setSymRef(arrayPointer, newSymRef);
		} else if (operand instanceof DereferenceExpression) {
			// &(*p) = p, so just evaluate the pointer and return.
			result = evaluate(state, pid,
					((DereferenceExpression) operand).pointer());
		} else if (operand instanceof DotExpression) {
			DotExpression dot = (DotExpression) operand;
			int index = dot.fieldIndex();

			if (dot.isStruct()) {
				Evaluation eval = reference(state, pid,
						(LHSExpression) dot.structOrUnion());
				SymbolicExpression structPointer = eval.value;
				ReferenceExpression oldSymRef = symbolicUtil
						.getSymRef(structPointer);
				ReferenceExpression newSymRef = universe
						.tupleComponentReference(oldSymRef,
								universe.intObject(index));

				eval.value = symbolicUtil.setSymRef(structPointer, newSymRef);
				result = eval;
			} else {
				// when u is a union type, then &(u.x) = &u.
				return reference(state, pid,
						(LHSExpression) dot.structOrUnion());
			}
		} else
			throw new CIVLInternalException("Unknown kind of LHSExpression",
					operand);
		return result;
	}

	public StateFactory stateFactory() {
		return stateFactory;
	}

	@Override
	public SymbolicUtility symbolicUtility() {
		return symbolicUtil;
	}

	public SymbolicUniverse universe() {
		return universe;
	}

	@Override
	public Pair<Evaluation, NumericExpression[]> evaluatePointerAdd(
			State state, String process, SymbolicExpression ptr,
			NumericExpression offset, boolean ifCheckOutput, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression newPtr = symbolicUtil.makePointer(ptr,
				symbolicAnalyzer.getMemBaseReference(state, ptr, source));

		return this.pointerAddWorker(state, process, newPtr, offset,
				ifCheckOutput, source);
	}

	@Override
	public List<ReferenceExpression> leafNodeReferencesOfType(
			CIVLSource source, State state, int pid, CIVLType type)
			throws UnsatisfiablePathConditionException {
		return this.leafNodeReferencesOfType(source, state, pid, type,
				universe.identityReference());
	}

	private List<ReferenceExpression> leafNodeReferencesOfType(
			CIVLSource source, State state, int pid, CIVLType type,
			ReferenceExpression parent)
			throws UnsatisfiablePathConditionException {
		List<ReferenceExpression> result = new ArrayList<>();
		TypeKind typeKind = type.typeKind();

		switch (typeKind) {
		case ARRAY:
			throw new CIVLUnimplementedFeatureException(
					"sub-references of incomplete arrays", source);

		case COMPLETE_ARRAY: {
			CIVLCompleteArrayType arrayType = (CIVLCompleteArrayType) type;
			Expression extent = arrayType.extent();
			Evaluation eval = this.evaluate(state, pid, extent);
			NumericExpression extentValue = (NumericExpression) eval.value;
			CIVLType eleType = arrayType.elementType();

			state = eval.state;

			Reasoner reasoner = universe.reasoner(state.getPathCondition());
			IntegerNumber length_number = (IntegerNumber) reasoner
					.extractNumber(extentValue);

			if (length_number != null) {
				int length_int = length_number.intValue();

				for (int i = 0; i < length_int; i++) {
					ArrayElementReference arrayEle = universe
							.arrayElementReference(parent, universe.integer(i));

					result.addAll(this.leafNodeReferencesOfType(source, state,
							pid, eleType, arrayEle));
				}
			} else
				throw new CIVLUnimplementedFeatureException(
						"sub-references of arrays with non-concrete extent",
						source);
			break;
		}
		case DOMAIN:
		case ENUM:
		case POINTER:
		case BUNDLE:
		case PRIMITIVE:
			result.add(parent);
			break;
		case STRUCT_OR_UNION: {
			CIVLStructOrUnionType structOrUnion = (CIVLStructOrUnionType) type;
			int numFields = structOrUnion.numFields();

			if (structOrUnion.isUnionType())
				throw new CIVLUnimplementedFeatureException(
						"sub-references of union type", source);
			for (int i = 0; i < numFields; i++) {
				CIVLType filedType = structOrUnion.getField(i).type();
				TupleComponentReference tupleComp = universe
						.tupleComponentReference(parent, universe.intObject(i));

				result.addAll(this.leafNodeReferencesOfType(source, state, pid,
						filedType, tupleComp));
			}
			break;
		}
		default:
			throw new CIVLUnimplementedFeatureException("sub-references of "
					+ typeKind, source);
		}
		return result;
	}

	@Override
	public Pair<State, SymbolicArrayType> evaluateCIVLArrayType(State state,
			int pid, CIVLArrayType type)
			throws UnsatisfiablePathConditionException {
		Pair<State, SymbolicArrayType> ret_pair;
		Evaluation eval;
		NumericExpression extent;

		if (!type.isComplete()) {
			// since type is CIVLArrayType, following cast should be safe.
			ret_pair = new Pair<>(state,
					(SymbolicArrayType) type.getDynamicType(universe));
			return ret_pair;
		}
		// if type is complete array type, get extent.
		eval = this.evaluate(state, pid,
				((CIVLCompleteArrayType) type).extent());
		extent = (NumericExpression) eval.value;
		if (!type.elementType().isArrayType()) {
			SymbolicArrayType ret_type = universe.arrayType(type.elementType()
					.getDynamicType(universe), extent);

			state = eval.state;
			ret_pair = new Pair<>(state, ret_type);
			return ret_pair;
		} else {
			SymbolicArrayType ret_type;

			// This branch comes from
			// "if element type of 'type' has an array type", so following cast
			// is safe.
			ret_pair = this.evaluateCIVLArrayType(state, pid,
					(CIVLArrayType) type.elementType());
			ret_type = universe.arrayType(ret_pair.right, extent);
			ret_pair.right = ret_type;
			return ret_pair;
		}
	}

	@Override
	public MemoryUnitExpressionEvaluator memoryUnitEvaluator() {
		return this.memUnitEvaluator;
	}

	/**
	 * Logging an out of bound error caused by pointer addition. Returns the new
	 * state after logging.
	 * 
	 * @param source
	 *            The {@link CIVLSource} of the pointer addition statement
	 * @param state
	 *            The current state
	 * @param process
	 *            The String identifier of the process
	 * @param claim
	 *            The failure bound checking predicate
	 * @param resultType
	 *            The {@link ResultType} of the result of reasoning the bound
	 *            checking predicate
	 * @param array
	 *            The {@link SymbolicExpression} of the array on where the
	 *            pointer addition happens.
	 * @param pointer
	 *            The pointer of the pointer addition operation
	 * @param offset
	 *            The offset of the pointer addition operation
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State reportPtrAddOutOfBoundError(CIVLSource source, State state,
			String process, BooleanExpression claim, ResultType resultType,
			SymbolicExpression array, SymbolicExpression pointer,
			SymbolicExpression offset, boolean multiDimensional)
			throws UnsatisfiablePathConditionException {
		String msg = (multiDimensional) ? "Array object"
				: "A allocated sequence of memory space";

		return errorLogger.logError(
				source,
				state,
				process,
				symbolicAnalyzer.stateInformation(state),
				claim,
				resultType,
				ErrorKind.OUT_OF_BOUNDS,
				"Pointer addition results in an index out of bound error on "
						+ msg
						+ ": "
						+ symbolicAnalyzer.symbolicExpressionToString(source,
								state, null, array)
						+ "\nOriginal pointer: "
						+ symbolicAnalyzer.symbolicExpressionToString(source,
								state, null, pointer)
						+ "\nPointer addtion offset: "
						+ symbolicAnalyzer.symbolicExpressionToString(source,
								state, null, offset));
	}

	/**
	 * pre-condition:
	 * <ol>
	 * <li>The object pointed by the "pointer" must have an array type</li>
	 * <li>"reasoner" must be initialized</li>
	 * </ol>
	 * post-condition:
	 * <ol>
	 * <li>The left side of the pair must be an pointer, cannot be "null"</li>
	 * <li>The right side of the pair may be "null"</li>
	 * </ol>
	 * post-condition: A helper function for pointer addition. Recomputing array
	 * element referencing indices when more than one dimensional coordinates
	 * need to be changed.
	 * 
	 * @param state
	 *            The current state
	 * @param process
	 *            The String identifier of the process
	 * @param pointedVid
	 *            The variable id of the pointed array object
	 * @param pointedSid
	 *            The variable id of the pointed array object
	 * @param pointer
	 *            The pointer points to the array object
	 * @param offset
	 *            The offset added to the pointer
	 * @param reasoner
	 *            An instance reference of a {@link Reasoner} object
	 * @param source
	 *            The CIVLSource of the statement
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Pair<Evaluation, NumericExpression[]> recomputeArrayIndices(
			State state, String process, int pointedVid, int pointedSid,
			SymbolicExpression pointer, NumericExpression offset,
			Reasoner reasoner, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		NumericExpression newIndex, totalOffset = zero;
		NumericExpression sliceSize = one;
		SymbolicExpression arrayRootPtr, wholeArray;
		NumericExpression[] indices, coordinateSizes, sliceSizes, oldIndices;
		BooleanExpression claim;
		ReferenceExpression oldRef, newRef;
		ResultType resultType;
		Evaluation eval;
		int dim;

		arrayRootPtr = symbolicUtil.arrayRootPtr(pointer, source);
		eval = dereference(source, state, process, null, arrayRootPtr, false);
		state = eval.state;
		wholeArray = eval.value;
		coordinateSizes = symbolicUtil
				.arrayCoordinateSizes((SymbolicCompleteArrayType) eval.value
						.type());
		sliceSizes = symbolicUtil.arraySlicesSizes(coordinateSizes);
		dim = coordinateSizes.length;
		oldRef = symbolicAnalyzer.getMemBaseReference(state, pointer, source);
		assert oldRef.isArrayElementReference();
		oldIndices = symbolicUtil
				.stripIndicesFromReference((ArrayElementReference) oldRef);
		// computes total offset from the first element
		for (int i = 0; i < dim; i++) {
			NumericExpression oldIndex;

			oldIndex = oldIndices[i];
			sliceSize = sliceSizes[i];
			totalOffset = universe.add(totalOffset,
					universe.multiply(oldIndex, sliceSize));
		}
		totalOffset = universe.add(totalOffset, offset);
		// if totalOffset less than zero, report error
		claim = universe.lessThanEquals(zero, totalOffset);
		resultType = reasoner.valid(claim).getResultType();
		if (!resultType.equals(ResultType.YES))
			state = this.reportPtrAddOutOfBoundError(source, state, process,
					claim, resultType, wholeArray, pointer, offset, false);
		// Computes new indexes
		indices = new NumericExpression[dim];
		for (int i = 0; i < dim; i++) {
			BooleanExpression checkClaim;
			ResultType checkResultType;
			Pair<NumericExpression, NumericExpression> newIndex_remainder;

			sliceSize = sliceSizes[i];
			newIndex_remainder = symbolicUtil.arithmeticIntDivide(totalOffset,
					sliceSize);
			newIndex = newIndex_remainder.left;
			totalOffset = newIndex_remainder.right;
			checkClaim = universe.lessThan(newIndex, coordinateSizes[i]);
			// TODO change to andTo
			checkResultType = reasoner.valid(checkClaim).getResultType();
			if (!checkResultType.equals(ResultType.YES)) {
				BooleanExpression equalExtentClaim = universe.equals(newIndex,
						coordinateSizes[i]);

				checkResultType = reasoner.valid(equalExtentClaim)
						.getResultType();
				if (checkResultType.equals(ResultType.YES)) {
					if (i < dim - 1) {
						newIndex = universe.subtract(newIndex, one);
						totalOffset = universe.add(totalOffset, sliceSizes[i]);
					}
				} else
					state = this.reportPtrAddOutOfBoundError(source, state,
							process, equalExtentClaim, checkResultType,
							wholeArray, pointer, offset, false);
			}
			indices[i] = newIndex;
		}
		// if totalOffset still not equal to zero, report error
		claim = universe.equals(totalOffset, zero);
		resultType = reasoner.valid(claim).getResultType();
		if (!resultType.equals(ResultType.YES))
			state = this.reportPtrAddOutOfBoundError(source, state, process,
					claim, resultType, wholeArray, pointer, offset, false);
		newRef = symbolicUtil.makeArrayElementReference(
				symbolicUtil.getSymRef(arrayRootPtr), indices);
		eval = new Evaluation(state, symbolicUtil.makePointer(pointedSid,
				pointedVid, newRef));
		return new Pair<>(eval, sliceSizes);
	}

	@Override
	public SymbolicAnalyzer symbolicAnalyzer() {
		return this.symbolicAnalyzer;
	}

	@Override
	public Evaluation evaluate(State state, int pid, Expression expression)
			throws UnsatisfiablePathConditionException {
		return this.evaluate(state, pid, expression, true);
	}
}
