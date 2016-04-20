package edu.udel.cis.vsl.civl.semantics;

import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.udel.cis.vsl.civl.err.CIVLException;
import edu.udel.cis.vsl.civl.err.CIVLExecutionException;
import edu.udel.cis.vsl.civl.err.CIVLExecutionException.Certainty;
import edu.udel.cis.vsl.civl.err.CIVLExecutionException.ErrorKind;
import edu.udel.cis.vsl.civl.err.CIVLInternalException;
import edu.udel.cis.vsl.civl.err.CIVLStateException;
import edu.udel.cis.vsl.civl.err.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.err.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.kripke.Enabler;
import edu.udel.cis.vsl.civl.log.CIVLLogEntry;
import edu.udel.cis.vsl.civl.model.IF.AbstractFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
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
import edu.udel.cis.vsl.civl.model.IF.expression.Expression.ExpressionKind;
import edu.udel.cis.vsl.civl.model.IF.expression.FunctionPointerExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.HereOrRootExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.InitialValueExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.IntegerLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.QuantifiedExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.RealLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ResultExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ScopeofExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SelfExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SizeofExpressionExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SizeofTypeExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.StringLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.StructOrUnionLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SubscriptExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SystemGuardExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.WaitGuardExpression;
import edu.udel.cis.vsl.civl.model.IF.statement.WaitStatement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLBundleType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLCompleteArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLEnumType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLHeapType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPointerType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPrimitiveType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPrimitiveType.PrimitiveTypeKind;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLStructOrUnionType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.type.StructOrUnionField;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.state.IF.DynamicScope;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.util.Pair;
import edu.udel.cis.vsl.civl.util.Singleton;
import edu.udel.cis.vsl.gmc.ErrorLog;
import edu.udel.cis.vsl.gmc.GMCConfiguration;
import edu.udel.cis.vsl.sarl.IF.ModelResult;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SARLException;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.ValidityResult;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.ArrayElementReference;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NTReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.OffsetReference;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicUnionType;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicCollection;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicSequence;
import edu.udel.cis.vsl.sarl.ideal.common.NTPrimitivePower;
import edu.udel.cis.vsl.sarl.number.Numbers;

/**
 * An evaluator is used to evaluate expressions.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class CommonEvaluator implements Evaluator {

	/* *************************** Instance Fields ************************* */

	private Enabler enabler;

	/**
	 * An uninterpreted function used to evaluate "BigO" of an expression. It
	 * takes as input one expression of real type and return a real type.
	 */
	private SymbolicExpression bigOFunction;

	/**
	 * LinkedList used to store a stack of bound variables during evaluation of
	 * (possibly nested) quantified expressions. LinkedList is used instead of
	 * Stack because of its more intuitive iteration order.
	 */
	private LinkedList<SymbolicConstant> boundVariables = new LinkedList<SymbolicConstant>();

	/**
	 * The symbolic bundle type.
	 */
	private SymbolicUnionType bundleType;

	/**
	 * The gmc configuration.
	 */
	private GMCConfiguration config;

	/**
	 * The symbolic dynamic type.
	 */
	private SymbolicTupleType dynamicType;

	private SymbolicType gcommType;

	private SymbolicType commType;

	/**
	 * The symbolic heap type.
	 */
	private SymbolicTupleType heapType;

	/**
	 * TODO ????
	 */
	private ReferenceExpression identityReference;

	/**
	 * The error logging facility.
	 */
	private ErrorLog log;

	/**
	 * The unique model factory used in the system.
	 */
	private ModelFactory modelFactory;

	/**
	 * The symbolic expression of NULL expression, i.e., the undefined value.
	 */
	private SymbolicExpression nullExpression;

	/**
	 * The symbolic expression of NULL pointer.
	 */
	private SymbolicExpression nullPointer;

	/**
	 * The unique real number factory used in the system.
	 */
	private NumberFactory numberFactory = Numbers.REAL_FACTORY;

	/**
	 * The symbolic numeric expression of 1.
	 */
	private NumericExpression one;

	/**
	 * The symbolic int object of 1.
	 */
	private IntObject oneObj;

	/**
	 * The pointer value is a triple <s,v,r> where s identifies the dynamic
	 * scope, v identifies the variable within that scope, and r identifies a
	 * point within that variable. The type of s is scopeType, which is just a
	 * tuple wrapping a single integer which is the dynamic scope ID number. The
	 * type of v is integer; it is the (static) variable ID number for the
	 * variable in its scope. The type of r is ReferenceExpression from SARL.
	 */
	private SymbolicTupleType pointerType;

	private SymbolicTupleType functionPointerType;

	/**
	 * TODO ???
	 */
	private Map<SymbolicType, NumericExpression> sizeofDynamicMap = new HashMap<>();

	/**
	 * An uninterpreted function used to evaluate "sizeof" on a type. It takes
	 * as input one expression of type dynamicType and returns an integer
	 * expression.
	 */
	private SymbolicExpression sizeofFunction;

	/**
	 * Solve for concrete counterexamples?
	 */
	private boolean solve = false;

	/**
	 * The unique state factory used in the system.
	 */
	private StateFactory stateFactory;

	/**
	 * Reasoner with trivial context "true". Used to determine satisfiability of
	 * path conditions.
	 */
	private Reasoner trueReasoner;

	/**
	 * The symbolic int object of 2.
	 */
	private IntObject twoObj;

	/**
	 * Map from symbolic type to a canonic symbolic expression of that type.
	 */
	private Map<SymbolicType, SymbolicExpression> typeExpressionMap = new HashMap<SymbolicType, SymbolicExpression>();

	/**
	 * The unique symbolic universe used in the system.
	 */
	private SymbolicUniverse universe;

	/**
	 * The symbolic int object of 0.
	 */
	private IntObject zeroObj;

	/**
	 * The symbolic numeric expression of 0.
	 */
	private NumericExpression zero;

	/**
	 * The symbolic numeric expression of ? TODO
	 */
	private NumericExpression zeroR;

	/* ***************************** Constructors ************************** */

	/**
	 * Create a new instance of evaluator for evaluating expressions.
	 * 
	 * @param config
	 *            The GMC configuration.
	 * @param modelFactory
	 *            The model factory to be used.
	 * @param stateFactory
	 *            The state factory to be used.
	 * @param log
	 *            The error logging facility.
	 */
	public CommonEvaluator(GMCConfiguration config, ModelFactory modelFactory,
			StateFactory stateFactory, ErrorLog log) {
		SymbolicType dynamicToIntType;

		this.config = config;
		this.modelFactory = modelFactory;
		this.stateFactory = stateFactory;
		this.universe = stateFactory.symbolicUniverse();
		dynamicType = modelFactory.dynamicSymbolicType();
		pointerType = modelFactory.pointerSymbolicType();
		functionPointerType = modelFactory.functionPointerSymbolicType();
		heapType = modelFactory.heapSymbolicType();
		bundleType = modelFactory.bundleSymbolicType();
		this.log = log;
		zeroObj = (IntObject) universe.canonic(universe.intObject(0));
		oneObj = (IntObject) universe.canonic(universe.intObject(1));
		twoObj = (IntObject) universe.canonic(universe.intObject(2));
		identityReference = (ReferenceExpression) universe.canonic(universe
				.identityReference());
		zero = (NumericExpression) universe.canonic(universe.integer(0));
		zeroR = (NumericExpression) universe.canonic(universe.zeroReal());
		one = (NumericExpression) universe.canonic(universe.integer(1));
		nullPointer = universe.canonic(makePointer(-1, -1,
				universe.nullReference()));
		nullExpression = universe.nullExpression();
		dynamicToIntType = universe.functionType(new Singleton<SymbolicType>(
				dynamicType), universe.integerType());
		sizeofFunction = universe.symbolicConstant(
				universe.stringObject("SIZEOF"), dynamicToIntType);
		sizeofFunction = universe.canonic(sizeofFunction);
		bigOFunction = universe.symbolicConstant(
				universe.stringObject("BIG_O"), universe.functionType(
						new Singleton<SymbolicType>(universe.realType()),
						universe.realType()));
		bigOFunction = universe.canonic(bigOFunction);
		trueReasoner = universe.reasoner(universe.trueExpression());
		if (modelFactory.model().gcommType() != null)
			gcommType = modelFactory.model().gcommType()
					.getDynamicType(universe);
		if (modelFactory.model().commType() != null)
			commType = modelFactory.model().commType().getDynamicType(universe);
	}

	/* ************************** Private Methods ************************** */

	/**
	 * Computes the symbolic initial value of a variable.
	 * 
	 * @param variable
	 *            The variable to be evaluated.
	 * @param dynamicType
	 *            The symbolic type of the variable.
	 * @param dyscopeId
	 *            The dynamic scope ID of the current state.
	 * @return The symbolic initial value of the given variable
	 */
	private SymbolicExpression computeInitialValue(Variable variable,
			SymbolicType dynamicType, int dyscopeId) {
		CIVLType type = variable.type();
		int vid = variable.vid();
		SymbolicExpression result;

		if (!variable.isInput()
				&& !variable.isBound()
				&& (type instanceof CIVLPrimitiveType || type instanceof CIVLPointerType)) {
			result = nullExpression;
		} else {
			StringObject name = universe.stringObject("X_s" + dyscopeId + "v"
					+ vid);

			result = universe.symbolicConstant(name, dynamicType);
		}
		return result;
	}

	/**
	 * Given an expression of pointer type, evaluates that expression in the
	 * given state to get a pointer value, and then dereferences that to yield
	 * the value pointed to.
	 * 
	 * @param state
	 *            a CIVL model state
	 * @param pid
	 *            PID of the process in which this evaluation occurs
	 * @param operand
	 *            an expression of pointer type
	 * @return the referenced value
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation dereference(State state, int pid, Expression operand)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, operand);

		return dereference(operand.getSource(), eval.state, eval.value);
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
	private Evaluation dynamicTypeOf(State state, int pid, CIVLType type,
			CIVLSource source, boolean isDefinition)
			throws UnsatisfiablePathConditionException {
		TypeEvaluation typeEval = getDynamicType(state, pid, type, source,
				isDefinition);
		SymbolicExpression expr = expressionOfType(typeEval.type);
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

		for (Variable param : function.parameters()) {
			argumentTypes.add(param.type().getDynamicType(universe));
		}
		for (Expression arg : expression.arguments()) {
			Evaluation eval = evaluate(state, pid, arg);
			arguments.add(eval.value);
		}
		functionType = universe.functionType(argumentTypes, returnType);
		functionExpression = universe.symbolicConstant(
				universe.stringObject(function.name().name()), functionType);
		functionApplication = universe.apply(functionExpression, arguments);
		result = new Evaluation(state, functionApplication);
		return result;
	}

	/**
	 * Evaluates an address-of expression "&e".
	 * 
	 * @param state
	 *            the pre-state
	 * @param pid
	 *            PID of the process performing the evaluation
	 * @param expression
	 *            the address-of expression
	 * @return the symbolic expression of pointer type resulting from evaluating
	 *         the address of the argument and a new state (if there is
	 *         side-effect, otherwise just return the orginal state)
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateAddressOf(State state, int pid,
			AddressOfExpression expression)
			throws UnsatisfiablePathConditionException {
		return reference(state, pid, expression.operand());
	}

	/**
	 * Evaluates a short-circuit "and" expression "p&&q".
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
		BooleanExpression p = (BooleanExpression) eval.value;
		BooleanExpression assumption = eval.state.getPathCondition();
		Reasoner reasoner = universe.reasoner(assumption);

		if (reasoner.isValid(p))
			return evaluate(eval.state, pid, expression.right());
		if (reasoner.isValid(universe.not(p))) {
			eval.value = universe.falseExpression();
			return eval;
		} else {
			BooleanExpression assumptionAndp = universe.and(assumption, p);
			State s1 = eval.state.setPathCondition(assumptionAndp);
			Evaluation eval1 = evaluate(s1, pid, expression.right());
			BooleanExpression pcTemp = eval1.state.getPathCondition();

			if (!assumptionAndp.equals(pcTemp)) {
				BooleanExpression pc = universe.or(pcTemp,
						universe.and(assumption, universe.not(p)));

				eval.state = eval.state.setPathCondition(pc);
			}
			// Reason for above: In the common case where there
			// are no side effects, this would set the path condition to
			// (assumption && p) || (assumption && !p),
			// which does not get simplified to just "assumption",
			// as one would like. So it is handled as a special case:
			// check whether pcTemp equals assumption && p
			// (i.e., the evaluation of expression.right() did not
			// add any side-effects). If this holds, then pc is just
			// assumption.
			eval.value = universe.and(p, (BooleanExpression) eval1.value);
			return eval;
		}
	}

	/**
	 * Evaluate an array literal expression.
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
		SymbolicType symbolicElementType = expression.elementType()
				.getDynamicType(universe);
		List<SymbolicExpression> symbolicElements = new ArrayList<>();
		Evaluation eval;

		for (Expression element : elements) {
			eval = evaluate(state, pid, element);
			symbolicElements.add(eval.value);
			state = eval.state;
		}
		return new Evaluation(state, universe.array(symbolicElementType,
				symbolicElements));
	}

	/**
	 * Evaluate a binary expression.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The binary expression.
	 * @return A symbolic expression for the binary operation and a new state if
	 *         there is side-effect.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateBinary(State state, int pid,
			BinaryExpression expression)
			throws UnsatisfiablePathConditionException {
		BINARY_OPERATOR operator = expression.operator();

		if (operator == BINARY_OPERATOR.AND)
			return evaluateAnd(state, pid, expression);
		if (operator == BINARY_OPERATOR.OR)
			return evaluateOr(state, pid, expression);
		if (operator == BINARY_OPERATOR.IMPLIES)
			return evaluateImplies(state, pid, expression);
		else {
			if (expression.left().getExpressionType()
					.equals(modelFactory.scopeType())) {
				return evaluateScopeOperations(state, pid, expression);
			} else {
				return evaluateNumericOperations(state, pid, expression);
			}
		}
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
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The cast expression.
	 * @return The symbolic representation of the cast expression.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateCast(State state, int pid,
			CastExpression expression)
			throws UnsatisfiablePathConditionException {
		Expression arg = expression.getExpression();
		CIVLType argType = arg.getExpressionType();
		Evaluation eval = evaluate(state, pid, arg);
		SymbolicExpression value = eval.value;
		CIVLType castType = expression.getCastType();
		TypeEvaluation typeEval = getDynamicType(eval.state, pid, castType,
				expression.getSource(), false);
		SymbolicType endType = typeEval.type;

		state = typeEval.state;
		if (argType.isBoolType() && castType.isIntegerType()) {
			boolean boolv = universe.extractBoolean((BooleanExpression) value);

			if (boolv) {
				eval.value = universe.integer(1);
			} else
				eval.value = universe.integer(0);
			return eval;
		} else if (argType.isIntegerType() && castType.isPointerType()) {
			// only good cast is from 0 to null pointer
			BooleanExpression assumption = state.getPathCondition();
			BooleanExpression claim = universe.equals(zero, value);
			ResultType resultType = universe.reasoner(assumption).valid(claim)
					.getResultType();

			if (resultType != ResultType.YES) {
				state = logError(expression.getSource(), state, claim,
						resultType, ErrorKind.INVALID_CAST,
						"Cast from non-zero integer to pointer");
				eval.state = state;
			}
			eval.value = nullPointer;
			return eval;
		} else if (argType.isPointerType() && castType.isPointerType()) {
			// pointer to pointer: for now...no change.
			return eval;
		}
		try {
			eval.value = universe.cast(endType, eval.value);
		} catch (SARLException e) {
			CIVLStateException error = new CIVLStateException(
					ErrorKind.INVALID_CAST, Certainty.NONE,
					"SARL could not cast: " + e, eval.state,
					expression.getSource());

			reportError(error);
			throw new UnsatisfiablePathConditionException();
		}
		return eval;
	}

	/**
	 * Evaluate a char literal expression.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The char literal expression.
	 * @return The symbolic representation of the char literal expression.
	 */
	private Evaluation evaluateCharLiteral(State state, int pid,
			CharLiteralExpression expression) {
		return new Evaluation(state, universe.character(expression.value()));
	}

	/**
	 * Evaluates a conditional expression.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            the pid of the currently executing process.
	 * @param expression
	 *            The conditional expression.
	 * @return A symbolic expression for the result of the conditional.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateCond(State state, int pid,
			ConditionalExpression expression)
			throws UnsatisfiablePathConditionException {
		return evaluateConditional(state, pid, expression.getCondition(),
				expression.getTrueBranch(), expression.getFalseBranch());
	}

	/**
	 * <p>
	 * General method for evaluating "short-circuited" conditional expressions
	 * that may involve logged side-effects on the path condition. These include
	 * expressions of the form <code>c?t:f</code>, <code>p&&q</code>, and
	 * <code>p||q</code>. The latter two are a special case of the first:
	 * <ul>
	 * <li><code>p&&q</code> is equivalent to <code>p?q:false</code></li>
	 * <li><code>p||q</code> is equivalent to <code>p?true:q</code></li>
	 * </ul>
	 * </p>
	 * 
	 * <p>
	 * Say the path condition is <code>p</code> and the expression is
	 * <code>(c?t:f)</code>.
	 * </p>
	 * 
	 * <p>
	 * If <code>c</code> is valid (assuming <code>p</code>), the result is just
	 * the result of evaluating <code>t</code>. If <code>!c</code> is valid, the
	 * result is just the result of evaluating <code>f</code>. The subtle case
	 * is where neither of those is valid, in which case, proceed as follows:
	 * </p>
	 * 
	 * <p>
	 * When evaluating <code>t</code>, assume <code>c</code> holds. When
	 * evaluating <code>f</code>, assume <code>!c</code> holds. Say
	 * <code>eval(p&&c, t)</code> results in <code>(p1,v1)</code> and
	 * <code>eval(p&&!c,f)</code> results in <code>(p2,v2)</code>. Then return
	 * <code>(p1||p2, (c?v1:v2))</code>.
	 * </p>
	 * 
	 * <p>
	 * Example: <code>x==0 ? 1/w + y/(1-x) : 1/z + y/x</code>, <code>p</code>=
	 * <code>true</code>. <code>eval(p&&c, t)</code> yields
	 * <code>(x==0 && w!=0, 1/w+y/(1-x))</code> together with a logged warning
	 * that <code>w!=0</code> has been assumed. <code>eval(p&&!c,f)</code>
	 * yields <code>(x!=0 && z!=0, 1/z+y/x)</code> together with a logged
	 * warning that <code>z!=0</code> has been assumed. The resulting path
	 * condition is <code>(x==0 && w!=0) || (x!=0 && z!=0)</code>.
	 * </p>
	 * 
	 * @param state
	 *            the pre-state
	 * @param pid
	 *            PID of process evaluating this expression
	 * @param condition
	 *            the boolean conditional expression <code>c</code>
	 * @param trueBranch
	 *            the sub-expression which becomes the value if <code>c</code>
	 *            evaluates to <code>true</code>
	 * @param falseBranch
	 *            the sub-expression which becomes the value if <code>c</code>
	 *            evaluates to <code>false</code>
	 * @return the evaluation with the properly updated state and the
	 *         conditional value
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateConditional(State state, int pid,
			Expression condition, Expression trueBranch, Expression falseBranch)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, condition);
		BooleanExpression c = (BooleanExpression) eval.value;
		BooleanExpression assumption = eval.state.getPathCondition();
		Reasoner reasoner = universe.reasoner(assumption);

		if (reasoner.isValid(c))
			return evaluate(eval.state, pid, trueBranch);
		if (reasoner.isValid(universe.not(c)))
			return evaluate(eval.state, pid, falseBranch);
		else {
			BooleanExpression pc1 = universe.and(assumption, c);
			State s1 = eval.state.setPathCondition(pc1);
			BooleanExpression pc2 = universe.and(assumption, universe.not(c));
			State s2 = eval.state.setPathCondition(pc2);
			Evaluation eval1 = evaluate(s1, pid, trueBranch);
			Evaluation eval2 = evaluate(s2, pid, falseBranch);
			BooleanExpression newpc1 = eval1.state.getPathCondition();
			BooleanExpression newpc2 = eval2.state.getPathCondition();

			if (pc1 == newpc1 && pc2 == newpc2) {
				// no side effects from evaluating either branch
				// eval.state.pathCondition is assumption
			} else {
				eval.state = eval.state.setPathCondition(universe.or(
						eval1.state.getPathCondition(),
						eval2.state.getPathCondition()));
			}
			eval.value = universe.cond(c, eval1.value, eval2.value);
			return eval;
		}
	}

	/**
	 * Evaluates a dereference expression "*e".
	 * 
	 * @param state
	 *            the pre-state
	 * @param pid
	 *            PID of the process performing the evaluation
	 * @param expression
	 *            the dereference expression
	 * @return the symbolic expression value that result from dereferencing the
	 *         pointer value argument
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateDereference(State state, int pid,
			DereferenceExpression expression)
			throws UnsatisfiablePathConditionException {
		return dereference(state, pid, expression.pointer());
	}

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
	 * Evaluate a "dot" expression used to navigate to a field in a record,
	 * "e.f".
	 * 
	 * @param state
	 *            The state of the model
	 * @param pid
	 *            The pid of the process evaluating this expression
	 * @param expression
	 *            The dot expression
	 * @return The symbolic expression resulting from evaluating the expression
	 *         together with the post-state which may incorporate side-effects
	 *         resulting from the evaluation
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateDot(State state, int pid,
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
				logSimpleError(expression.getSource(), eval.state,
						ErrorKind.UNION,
						"Attempt to access an invalid union member");
				throw new UnsatisfiablePathConditionException();
			}
			eval.value = universe.unionExtract(universe.intObject(fieldIndex),
					structValue);
		}
		return eval;
	}

	private Evaluation evaluateDynamicTypeOf(State state, int pid,
			DynamicTypeOfExpression expression)
			throws UnsatisfiablePathConditionException {
		return dynamicTypeOf(state, pid, expression.getType(),
				expression.getSource(), true);
	}

	private Evaluation evaluateHereOrRootScope(State state, int pid,
			HereOrRootExpression expression) {
		int dyScopeID = expression.isRoot() ? state.rootScopeID() : state
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

	SymbolicExpression bigOExpression(SymbolicExpression expression) {
		SymbolicExpression result;

		if (expression.operator() == SymbolicOperator.POWER) {
			NumericExpression bigO;
			NumericExpression baseExpression;
			NumericExpression extractedPower;

			assert expression instanceof NTPrimitivePower;
			baseExpression = ((NTPrimitivePower) expression).primitive();
			extractedPower = universe.power(baseExpression,
					((NTPrimitivePower) expression).degree() - 1);
			bigO = (NumericExpression) universe.apply(bigOFunction,
					new Singleton<SymbolicExpression>(baseExpression));
			result = universe.multiply(extractedPower, bigO);
		} else {
			result = universe.apply(bigOFunction,
					new Singleton<SymbolicExpression>(expression));
		}
		return result;
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
		Evaluation result;
		TypeEvaluation typeEval = getDynamicType(state, pid, type,
				expression.getSource(), false);
		int sid = state.getScopeId(pid, variable);
		SymbolicExpression value = computeInitialValue(variable, typeEval.type,
				sid);

		result = new Evaluation(typeEval.state, value);
		return result;
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
			BinaryExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.left());
		SymbolicExpression left = eval.value;
		SymbolicExpression right;

		eval = evaluate(state, pid, expression.right());
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
			BooleanExpression claim = universe.neq(
					zeroOf(expression.getSource(),
							expression.getExpressionType()), denominator);
			ResultType resultType = universe.reasoner(assumption).valid(claim)
					.getResultType();

			if (resultType != ResultType.YES) {
				eval.state = logError(expression.getSource(), eval.state,
						claim, resultType, ErrorKind.DIVISION_BY_ZERO,
						"Division by zero");
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
		case EQUAL:
			this.isValueDefined(state, expression.left(), left);
			this.isValueDefined(state, expression.right(), right);
			eval.value = universe.equals(left, right);
			break;
		case NOT_EQUAL:
			this.isValueDefined(state, expression.left(), left);
			this.isValueDefined(state, expression.right(), right);
			eval.value = universe.neq(left, right);
			break;
		case MODULO: {
			BooleanExpression assumption = eval.state.getPathCondition();
			NumericExpression denominator = (NumericExpression) right;
			BooleanExpression claim = universe.neq(
					zeroOf(expression.getSource(),
							expression.getExpressionType()), denominator);
			ResultType resultType = universe.reasoner(assumption).valid(claim)
					.getResultType();

			// TODO: check not negative
			if (resultType != ResultType.YES) {
				eval.state = this.logError(expression.getSource(), eval.state,
						claim, resultType, ErrorKind.DIVISION_BY_ZERO,
						"Modulus denominator is zero");
			}
			eval.value = universe.modulo((NumericExpression) left, denominator);
			break;
		}
		case POINTER_ADD:
			eval = pointerAdd(state, pid, expression, left,
					(NumericExpression) right);
			break;
		case POINTER_SUBTRACT:
			eval = pointerSubtract(state, pid, expression, left, right);
			break;
		case IMPLIES:
		case AND:
		case OR:
			throw new CIVLInternalException("unreachable", expression);
		default:
			throw new CIVLUnimplementedFeatureException("Operator "
					+ expression.operator(), expression);
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
	private void isValueDefined(State state, Expression expression,
			SymbolicExpression expressionValue)
			throws UnsatisfiablePathConditionException {
		CIVLSource source = expression.getSource();
		CIVLType expressionType = expression.getExpressionType();

		if (expressionType.equals(modelFactory.scopeType())) {
			if (expressionValue.equals(modelFactory.undefinedScopeValue())) {
				logSimpleError(source, state, ErrorKind.MEMORY_LEAK,
						"Attempt to evaluate an invalid scope reference");
				throw new UnsatisfiablePathConditionException();
			}
		} else if (expressionType.equals(modelFactory.processType())) {
			if (expressionValue.equals(modelFactory.undefinedProcessValue())) {
				logSimpleError(source, state, ErrorKind.MEMORY_LEAK,
						"Attempt to evaluate an invalid process reference");
				throw new UnsatisfiablePathConditionException();
			}
		} else if (expressionValue.type().equals(this.pointerType)) {
			if (expressionValue.equals(nullPointer))
				return;
			try {
				int scopeID = this.getScopeId(source, expressionValue);

				if (scopeID < 0) {
					logSimpleError(source, state, ErrorKind.MEMORY_LEAK,
							"Attempt to evaluate a pointer refererring to memory of an invalid scope");
					throw new UnsatisfiablePathConditionException();
				}
			} catch (Exception e) {
				logSimpleError(source, state, ErrorKind.UNDEFINED_VALUE,
						"Attempt to use undefined pointer");
				throw new UnsatisfiablePathConditionException();
			}
		}
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

			assert lower.value instanceof NumericExpression;
			assert upper.value instanceof NumericExpression;
			rangeRestriction = universe.and(universe.lessThanEquals(
					(NumericExpression) lower.value,
					(NumericExpression) boundVariable), universe
					.lessThanEquals((NumericExpression) boundVariable,
							(NumericExpression) upper.value));
			stateWithRestriction = state.setPathCondition(universe.and(
					(BooleanExpression) rangeRestriction,
					state.getPathCondition()));
			quantifiedExpression = evaluate(stateWithRestriction, pid,
					expression.expression());
			switch (expression.quantifier()) {
			case EXISTS:
				result = new Evaluation(state, universe.existsInt(
						(NumericSymbolicConstant) boundVariable,
						(NumericExpression) lower.value,
						(NumericExpression) upper.value,
						(BooleanExpression) quantifiedExpression.value));
				break;
			case FORALL:
				result = new Evaluation(state, universe.forallInt(
						(NumericSymbolicConstant) boundVariable,
						(NumericExpression) lower.value,
						(NumericExpression) upper.value,
						(BooleanExpression) quantifiedExpression.value));
				break;
			case UNIFORM:
				result = new Evaluation(state, universe.forallInt(
						(NumericSymbolicConstant) boundVariable,
						(NumericExpression) lower.value,
						(NumericExpression) upper.value,
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
			result = stateFactory.isDesendantOf(state, right, left);
			eval.value = universe.bool(result);
			break;
		case LESS_THAN_EQUAL:
			result = (left == right) ? true : stateFactory.isDesendantOf(state,
					right, left);
			eval.value = universe.bool(result);
			break;
		case EQUAL:
			eval.value = universe.bool(left == right);
			break;
		case NOT_EQUAL:
			eval.value = universe.bool(left != right);
			break;
		default:
			throw new CIVLInternalException("unreachable",
					expression.getSource());
		}
		return eval;
	}

	private Evaluation evaluateSizeofExpressionExpression(State state, int pid,
			SizeofExpressionExpression expression)
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
	private Evaluation evaluateSubscript(State state, int pid,
			SubscriptExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.array());
		SymbolicExpression array = eval.value;
		SymbolicArrayType arrayType = (SymbolicArrayType) array.type();
		NumericExpression index;

		eval = evaluate(state, pid, expression.index());
		index = (NumericExpression) eval.value;
		if (arrayType.isComplete()) {
			NumericExpression length = universe.length(array);
			BooleanExpression assumption = eval.state.getPathCondition();
			BooleanExpression claim = universe.and(
					universe.lessThanEquals(zero, index),
					universe.lessThan(index, length));
			ResultType resultType = universe.reasoner(assumption).valid(claim)
					.getResultType();

			if (resultType != ResultType.YES) {
				eval.state = logError(expression.getSource(), eval.state,
						claim, resultType, ErrorKind.OUT_OF_BOUNDS,
						"Out of bounds array index:\nindex = " + index
								+ "\nlength = " + length);
			}
		}
		eval.value = universe.arrayRead(array, index);
		return eval;
	}

	private Evaluation evaluateSelf(State state, int pid,
			SelfExpression expression) {
		return new Evaluation(state, modelFactory.processValue(pid));
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

	private Evaluation evaluateResult(State state, int pid,
			ResultExpression expression) {
		// TODO
		// this is used in a contract post-condition as a variable to
		// refer to the result returned by a function. $result.
		// get rid of ResultExpression and instead create a variable
		// in the outermost scope of any function with non-void
		// return type, store the result of return in that variable.
		// Add method in Function to get that variable. (and set it?)
		// Model builder will translate $result to that variable.
		throw new CIVLUnimplementedFeatureException(
				"$result not yet implemented: " + expression.getSource());
	}

	/**
	 * Evaluate a string literal expression.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The string literal expression.
	 * @return The symbolic representation of the string literal expression.
	 */
	private Evaluation evaluateStringLiteral(State state, int pid,
			StringLiteralExpression expression) {
		return new Evaluation(state, universe.stringExpression(expression
				.value()));
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
			throw new CIVLInternalException("Unknown unary operator "
					+ expression.operator(), expression);
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
	private Evaluation evaluateVariable(State state, int pid,
			VariableExpression expression)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression value = state.valueOf(pid, expression.variable());

		if (value == null || value.isNull()) {
			CIVLExecutionException e = new CIVLStateException(
					ErrorKind.UNDEFINED_VALUE, Certainty.PROVEABLE,
					"Attempt to read uninitialized variable", state,
					expression.getSource());

			reportError(e);
			throw new UnsatisfiablePathConditionException();
		}
		return new Evaluation(state, value);
	}

	private Evaluation evaluateWaitGuard(State state, int pid,
			WaitGuardExpression expression) {
		SymbolicExpression joinProcess, guard;
		int pidValue;
		Evaluation eval;

		try {
			eval = evaluate(state, pid, expression.joinedProcess());
		} catch (UnsatisfiablePathConditionException e) {
			return new Evaluation(state, universe.falseExpression());
		}
		joinProcess = eval.value;
		state = eval.state;
		pidValue = modelFactory.getProcessId(expression.getSource(),
				joinProcess);
		if (!state.getProcessState(pidValue).hasEmptyStack())
			guard = universe.falseExpression();
		else
			guard = universe.trueExpression();
		return new Evaluation(state, guard);
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
	 */
	private Evaluation evaluateSystemGuard(State state, int pid,
			SystemGuardExpression expression) {
		return enabler.getSystemGuard(state, pid, expression);
	}

	/**
	 * Given a symbolic type, returns a canonic symbolic expression which
	 * somehow wraps that type so it can be used as a value. Nothing should be
	 * assumed about the symbolic expression. To extract the type from such an
	 * expression, use method {@link #getType}.
	 * 
	 * @param type
	 *            a symbolic type
	 * @return a canonic symbolic expression wrapping that type
	 */
	private SymbolicExpression expressionOfType(SymbolicType type) {
		SymbolicExpression result;

		type = (SymbolicType) universe.canonic(type);
		result = typeExpressionMap.get(type);
		if (result == null) {
			SymbolicExpression id = universe.integer(type.id());

			result = universe.canonic(universe.tuple(dynamicType,
					new Singleton<SymbolicExpression>(id)));
			typeExpressionMap.put(type, result);
		}
		return result;
	}

	/**
	 * Gets a concrete Java int from the field of a symbolic expression of tuple
	 * type or throws exception.
	 * 
	 * @param tuple
	 *            symbolic expression of tuple type
	 * @param fieldIndex
	 *            index of a field in that tuple
	 * @return the concrete int value of that field
	 * @throws CIVLInternalException
	 *             if a concrete integer value cannot be extracted
	 */
	private int extractIntField(CIVLSource source, SymbolicExpression tuple,
			IntObject fieldIndex) {
		NumericExpression field = (NumericExpression) universe.tupleRead(tuple,
				fieldIndex);

		return extractInt(source, field);
	}

	/**
	 * Finds pointers contained in a given expression recursively.
	 * 
	 * @param expr
	 * @param set
	 * @param state
	 */
	private void findPointersInExpression(SymbolicExpression expr,
			Set<SymbolicExpression> set, State state) {
		SymbolicType type = expr.type();

		// TODO check comm type
		if (type != null && !type.equals(heapType) && !type.equals(gcommType)
				&& !type.equals(commType) && !type.equals(bundleType)) {
			// need to eliminate heap type as well. each proc has its own.
			if (pointerType.equals(type)) {
				SymbolicExpression pointerValue;
				Evaluation eval;

				set.add(expr);
				try {
					if (getScopeId(null, expr) >= 0) {
						eval = this.dereference(null, state, expr);
						pointerValue = eval.value;
						state = eval.state;
						if (pointerValue.type() != null
								&& pointerValue.type().equals(pointerType))
							findPointersInExpression(pointerValue, set, state);
					}
				} catch (UnsatisfiablePathConditionException e) {
					// // TODO Auto-generated catch block
					// e.printStackTrace();
				}
			} else {
				int numArgs = expr.numArguments();

				for (int i = 0; i < numArgs; i++) {
					SymbolicObject arg = expr.argument(i);

					findPointersInObject(arg, set, state);
				}
			}
		}
	}

	/**
	 * Finds all the pointers that can be dereferenced inside a symbolic object.
	 * 
	 * @param object
	 *            a symbolic object
	 * @param set
	 *            a set to which the pointer values will be added
	 * @param heapType
	 *            the heap type, which will be ignored
	 */
	private void findPointersInObject(SymbolicObject object,
			Set<SymbolicExpression> set, State state) {
		switch (object.symbolicObjectKind()) {

		case EXPRESSION:
			findPointersInExpression((SymbolicExpression) object, set, state);
			break;
		case EXPRESSION_COLLECTION:
			for (SymbolicExpression expr : (SymbolicCollection<?>) object)
				findPointersInExpression(expr, set, state);
			break;
		default:
			// ignore types and primitives, they don't have any pointers
			// you can dereference.
		}
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

			result = new TypeEvaluation(state, getType(source, value));
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

			for (int i = 0; i < numFields; i++) {
				StructOrUnionField field = structType.getField(i);
				TypeEvaluation componentEval = getDynamicType(state, pid,
						field.type(), source, false);

				state = componentEval.state;
				componentTypes.add(componentEval.type);
			}
			result = new TypeEvaluation(state, universe.tupleType(structType
					.name().stringObject(), componentTypes));
		} else if (type instanceof CIVLBundleType) {
			result = new TypeEvaluation(state, type.getDynamicType(universe));
		} else if (type instanceof CIVLHeapType) {
			result = new TypeEvaluation(state, this.heapType);
		} else if (type instanceof CIVLEnumType) {
			result = new TypeEvaluation(state, type.getDynamicType(universe));
		} else
			throw new CIVLInternalException("Unreachable", source);
		return result;
	}

	/**
	 * Given a symbolic expression returned by the method
	 * {@link #expressionOfType}, this extracts the type that was used to create
	 * that expression. If the given expression is not an expression that was
	 * created by {@link #expressionOfType}, the behavior is undefined.
	 * 
	 * @param expr
	 *            a symbolic expression returned by method
	 *            {@link #expressionOfType}
	 * @return the symbolic type used to create that expression
	 */
	private SymbolicType getType(CIVLSource source, SymbolicExpression expr) {
		int id = extractIntField(source, expr, zeroObj);

		return (SymbolicType) universe.objectWithId(id);
	}

	/**
	 * Makes a pointer value from the given dynamic scope ID, variable ID, and
	 * symbolic reference value.
	 * 
	 * @param scopeId
	 *            ID number of a dynamic scope
	 * @param varId
	 *            ID number of a variable within that scope
	 * @param symRef
	 *            a symbolic reference to a point within the variable
	 * @return a pointer value as specified by the 3 components
	 */
	private SymbolicExpression makePointer(int scopeId, int varId,
			ReferenceExpression symRef) {
		SymbolicExpression scopeField = modelFactory.scopeValue(scopeId);
		SymbolicExpression varField = universe.integer(varId);
		SymbolicExpression result = universe.tuple(
				pointerType,
				Arrays.asList(new SymbolicExpression[] { scopeField, varField,
						symRef }));

		return result;
	}

	/**
	 * Evaluates pointer addition. Pointer addition involves the addition of a
	 * pointer expression and an integer.
	 * 
	 * @param state
	 *            the pre-state
	 * @param pid
	 *            the PID of the process evaluating the pointer addition
	 * @param expression
	 *            the pointer addition expression
	 * @param pointer
	 *            the result of evaluating argument 0 of expression
	 * @param offset
	 *            the result of evaluating argument 1 of expression
	 * @return the result of evaluating the sum of the pointer and the integer
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation pointerAdd(State state, int pid,
			BinaryExpression expression, SymbolicExpression pointer,
			NumericExpression offset)
			throws UnsatisfiablePathConditionException {
		ReferenceExpression symRef = getSymRef(pointer);

		if (symRef.isArrayElementReference()) {
			SymbolicExpression arrayPointer = parentPointer(
					expression.getSource(), pointer);
			Evaluation eval = dereference(expression.getSource(), state,
					arrayPointer);
			// eval.value is now a symbolic expression of array type.
			SymbolicArrayType arrayType = (SymbolicArrayType) eval.value.type();
			ArrayElementReference arrayElementRef = (ArrayElementReference) symRef;
			NumericExpression oldIndex = arrayElementRef.getIndex();
			NumericExpression newIndex = universe.add(oldIndex, offset);

			if (arrayType.isComplete()) { // check bounds
				NumericExpression length = universe.length(eval.value);
				BooleanExpression claim = universe.and(
						universe.lessThanEquals(zero, newIndex),
						universe.lessThanEquals(newIndex, length));
				BooleanExpression assumption = eval.state.getPathCondition();
				ResultType resultType = universe.reasoner(assumption)
						.valid(claim).getResultType();

				if (resultType != ResultType.YES) {
					eval.state = logError(expression.getSource(), eval.state,
							claim, resultType, ErrorKind.OUT_OF_BOUNDS,
							"Pointer addition resulted in out of bounds array index:\nindex = "
									+ newIndex + "\nlength = " + length);
				}
			}
			eval.value = setSymRef(pointer, universe.arrayElementReference(
					arrayElementRef.getParent(), newIndex));
			return eval;
		} else if (symRef.isOffsetReference()) {
			OffsetReference offsetRef = (OffsetReference) symRef;
			NumericExpression oldOffset = offsetRef.getOffset();
			NumericExpression newOffset = universe.add(oldOffset, offset);
			BooleanExpression claim = universe.and(
					universe.lessThanEquals(zero, newOffset),
					universe.lessThanEquals(newOffset, one));
			BooleanExpression assumption = state.getPathCondition();
			ResultType resultType = universe.reasoner(assumption).valid(claim)
					.getResultType();
			Evaluation eval;

			if (resultType != ResultType.YES) {
				state = logError(expression.getSource(), state, claim,
						resultType, ErrorKind.OUT_OF_BOUNDS,
						"Pointer addition resulted in out of bounds object pointer:\noffset = "
								+ newOffset);
			}
			eval = new Evaluation(state, setSymRef(pointer,
					universe.offsetReference(offsetRef.getParent(), newOffset)));
			return eval;
		} else
			throw new CIVLUnimplementedFeatureException(
					"Pointer addition for anything other than array elements or variables",
					expression);
	}

	/**
	 * Returns the set of pointer values that occur inside a symbolic
	 * expression, excluding any pointers that occur inside a heap. TODO
	 * Optimization: you only need to call this method on variables that could
	 * have pointers in them, otherwise don't bother
	 * 
	 * @param expr
	 *            a symbolic expression
	 * @param heapType
	 *            the heap type
	 * @return set of pointer values occurring a subexpression of expression
	 *         (including expression itself) but not in a heap
	 */

	private Set<SymbolicExpression> pointersInExpression(
			SymbolicExpression expr, State state) {
		Set<SymbolicExpression> result = new HashSet<>();

		findPointersInExpression(expr, result, state);
		return result;
	}

	/**
	 * Evaluates pointer subtraction.
	 * 
	 * @param state
	 *            the pre-state
	 * @param pid
	 *            the PID of the process performing this evaluation
	 * @param expression
	 *            the pointer subtraction expression
	 * @param p1
	 *            the result of evaluating argument 0 of expression; should be a
	 *            pointer
	 * @param p2
	 *            the result of evaluating argument 1 of expression; should be a
	 *            pointer
	 * @return the integer symbolic expression resulting from subtracting the
	 *         two pointers together with the post-state if side-effects
	 *         occurred
	 */
	private Evaluation pointerSubtract(State state, int pid,
			BinaryExpression expression, SymbolicExpression p1,
			SymbolicExpression p2) {
		throw new CIVLUnimplementedFeatureException("pointer subtraction",
				expression);
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

	/* ********************** Methods from Evaluator *********************** */

	@Override
	public Evaluation evaluate(State state, int pid, Expression expression)
			throws UnsatisfiablePathConditionException {
		ExpressionKind kind = expression.expressionKind();
		Evaluation result;

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
			result = evaluateBinary(state, pid, (BinaryExpression) expression);
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
			result = evaluateCast(state, pid, (CastExpression) expression);
			break;
		case CHAR_LITERAL:
			result = evaluateCharLiteral(state, pid,
					(CharLiteralExpression) expression);
			break;
		case COND:
			result = evaluateCond(state, pid,
					(ConditionalExpression) expression);
			break;
		case DEREFERENCE:
			result = evaluateDereference(state, pid,
					(DereferenceExpression) expression);
			break;
		case DERIVATIVE:
			result = evaluateDerivativeCall(state, pid,
					(DerivativeCallExpression) expression);
			break;
		case DOT:
			result = evaluateDot(state, pid, (DotExpression) expression);
			break;
		case DYNAMIC_TYPE_OF:
			result = evaluateDynamicTypeOf(state, pid,
					(DynamicTypeOfExpression) expression);
			break;
		case FUNCTION_POINTER:
			result = evaluateFunctionPointer(state, pid,
					(FunctionPointerExpression) expression);
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
		case RESULT:
			result = evaluateResult(state, pid, (ResultExpression) expression);
			break;
		case SCOPEOF:
			result = evaluateScopeofExpression(state, pid,
					(ScopeofExpression) expression);
			break;
		case SELF:
			result = evaluateSelf(state, pid, (SelfExpression) expression);
			break;
		case SIZEOF_TYPE:
			result = evaluateSizeofTypeExpression(state, pid,
					(SizeofTypeExpression) expression);
			break;
		case SIZEOF_EXPRESSION:
			result = evaluateSizeofExpressionExpression(state, pid,
					(SizeofExpressionExpression) expression);
			break;
		case STRING_LITERAL:
			result = evaluateStringLiteral(state, pid,
					(StringLiteralExpression) expression);
			break;
		case STRUCT_OR_UNION_LITERAL:
			result = evaluateStructOrUnionLiteral(state, pid,
					(StructOrUnionLiteralExpression) expression);
			break;
		case SUBSCRIPT:
			result = evaluateSubscript(state, pid,
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
			result = new Evaluation(state, modelFactory.undefinedProcessValue());
			break;
		case VARIABLE:
			result = evaluateVariable(state, pid,
					(VariableExpression) expression);
			break;
		case WAIT_GUARD:
			result = evaluateWaitGuard(state, pid,
					(WaitGuardExpression) expression);
			break;
		case QUANTIFIER:
			result = evaluateQuantifiedExpression(state, pid,
					(QuantifiedExpression) expression);
			break;
		default:
			throw new CIVLInternalException("Unknown kind of expression: "
					+ kind, expression.getSource());
		}
		return result;
	}

	private Evaluation evaluateFunctionPointer(State state, int pid,
			FunctionPointerExpression expression) {
		Scope scope = expression.scope();
		String function = expression.function().name().name();
		SymbolicExpression dyScopeId = modelFactory.scopeValue(state
				.getDyScope(pid, scope));
		SymbolicExpression functionPointer = universe.tuple(
				this.functionPointerType,
				Arrays.asList(new SymbolicExpression[] { dyScopeId,
						universe.stringExpression(function) }));

		return new Evaluation(state, functionPointer);
	}

	private Evaluation evaluateScopeofExpression(State state, int pid,
			ScopeofExpression expression)
			throws UnsatisfiablePathConditionException {
		LHSExpression argument = expression.argument();

		return scopeofExpression(state, pid, argument);
	}

	private Evaluation scopeofExpression(State state, int pid,
			LHSExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval;

		switch (expression.lhsExpressionKind()) {
		case DEREFERENCE:
			Expression pointer = ((DereferenceExpression) expression).pointer();

			eval = evaluate(state, pid, pointer);
			int sid = getScopeId(pointer.getSource(), eval.value);
			state = eval.state;
			if (sid < 0) {
				logSimpleError(pointer.getSource(), state,
						ErrorKind.DEREFERENCE,
						"Attempt to dereference pointer into scope which has been removed from state");
				throw new UnsatisfiablePathConditionException();
			}
			return new Evaluation(state, modelFactory.scopeValue(sid));
		case DOT:
			return scopeofExpression(state, pid,
					(LHSExpression) (((DotExpression) expression)
							.structOrUnion()));
		case SUBSCRIPT:
			return scopeofExpression(
					state,
					pid,
					(LHSExpression) (((SubscriptExpression) expression).array()));

		default:// VARIABLE
			int scopeId = state.getScopeId(pid,
					((VariableExpression) expression).variable());

			return new Evaluation(state, modelFactory.scopeValue(scopeId));
		}
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

			// TODO: this will modify state if state is mutable!
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
	public int extractInt(CIVLSource source, NumericExpression expression) {
		IntegerNumber result = (IntegerNumber) universe
				.extractNumber(expression);

		// TODO make expression

		if (result == null)
			throw new CIVLInternalException(
					"Unable to extract concrete int from " + expression, source);
		return result.intValue();
	}

	@Override
	public Evaluation dereference(CIVLSource source, State state,
			SymbolicExpression pointer)
			throws UnsatisfiablePathConditionException {
		// how to figure out if pointer is null pointer?
		try {
			int sid = getScopeId(source, pointer);

			if (sid < 0) {
				logSimpleError(source, state, ErrorKind.DEREFERENCE,
						"Attempt to dereference pointer into scope which has been removed from state");
				throw new UnsatisfiablePathConditionException();
			} else {
				int vid = getVariableId(source, pointer);
				ReferenceExpression symRef = getSymRef(pointer);
				SymbolicExpression variableValue = state.getScope(sid)
						.getValue(vid);
				SymbolicExpression deref;

				try {
					deref = universe.dereference(variableValue, symRef);
				} catch (SARLException e) {
					logSimpleError(
							source,
							state,
							ErrorKind.DEREFERENCE,
							"Illegal pointer dereference "
									+ source.getSummary());
					throw new UnsatisfiablePathConditionException();
				}
				return new Evaluation(state, deref);
			}
		} catch (CIVLInternalException e) {
			CIVLStateException se = new CIVLStateException(
					ErrorKind.DEREFERENCE, Certainty.MAYBE,
					"Undefined pointer value?", state, source);

			reportError(se);
			throw new UnsatisfiablePathConditionException();
		}
	}

	@Override
	public int findRank(SymbolicExpression comm, int pid) {
		SymbolicExpression place = this.universe.tupleRead(comm, zeroObj);
		return this.extractInt(null, (NumericExpression) place);
	}

	@Override
	public SymbolicExpression getParentPointer(SymbolicExpression pointer) {
		ReferenceExpression symRef = getSymRef(pointer);

		if (symRef instanceof NTReferenceExpression)
			return setSymRef(pointer,
					((NTReferenceExpression) symRef).getParent());
		return null;
	}

	@Override
	public Pair<State, CIVLFunction> evaluateFunctionExpression(State state,
			int pid, Expression functionExpression)
			throws UnsatisfiablePathConditionException {
		if (functionExpression == null)
			return null;
		else {
			CIVLFunction function;
			Evaluation eval = this.evaluate(state, pid, functionExpression);
			int scopeId = modelFactory.getScopeId(
					functionExpression.getSource(),
					universe.tupleRead(eval.value, this.zeroObj));
			SymbolicExpression symFuncName = universe.tupleRead(eval.value,
					this.oneObj);
			SymbolicSequence<?> originalArray = (SymbolicSequence<?>) symFuncName
					.argument(0);
			String funcName = "";

			state = eval.state;
			for (int j = 0; j < originalArray.size(); j++) {
				funcName += originalArray.get(j).toString().charAt(1);
			}
			function = state.getScope(scopeId).lexicalScope()
					.getFunction(funcName);
			return new Pair<>(state, function);
		}
	}

	@Override
	public int getScopeId(CIVLSource source, SymbolicExpression pointer) {
		return modelFactory.getScopeId(source,
				universe.tupleRead(pointer, zeroObj));
	}

	@Override
	public SymbolicExpression getSubArray(SymbolicExpression array,
			NumericExpression startIndex, NumericExpression endIndex,
			State state, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		// if startIndex is zero and endIndex is length, return array
		// verify startIndex >=0 and endIndex<= Length
		// if startIndex==endIndex return emptyArray
		// else if startIndex and endIndex are concrete, create concrete array
		// else need array lambdas or subsequence operation: todo
		BooleanExpression pathCondition = state.getPathCondition();
		Reasoner reasoner = universe.reasoner(pathCondition);
		NumericExpression length = universe.length(array);
		SymbolicArrayType arrayType = (SymbolicArrayType) array.type();
		SymbolicType elementType = arrayType.elementType();

		if (reasoner.isValid(universe.equals(zero, startIndex))
				&& reasoner.isValid(universe.equals(length, endIndex)))
			return array;
		else {
			BooleanExpression claim = universe.lessThanEquals(zero, startIndex);
			ResultType valid = reasoner.valid(claim).getResultType();

			if (valid != ResultType.YES) {
				state = logError(source, state, claim, valid,
						ErrorKind.OUT_OF_BOUNDS, "negative start index");
				pathCondition = state.getPathCondition();
				reasoner = universe.reasoner(pathCondition);
			}
			claim = universe.lessThanEquals(endIndex, length);
			valid = reasoner.valid(claim).getResultType();
			if (valid != ResultType.YES) {
				state = logError(source, state, claim, valid,
						ErrorKind.OUT_OF_BOUNDS,
						"end index exceeds length of array");
				pathCondition = state.getPathCondition();
				reasoner = universe.reasoner(pathCondition);
			}
			claim = universe.lessThanEquals(startIndex, endIndex);
			valid = reasoner.valid(claim).getResultType();
			if (valid != ResultType.YES) {
				state = logError(source, state, claim, valid,
						ErrorKind.OUT_OF_BOUNDS,
						"start index greater than end index");
				pathCondition = state.getPathCondition();
				reasoner = universe.reasoner(pathCondition);
			}
			if (reasoner.isValid(universe.equals(startIndex, endIndex))) {
				return universe.emptyArray(elementType);
			} else {
				IntegerNumber concreteStart = (IntegerNumber) reasoner
						.extractNumber(startIndex);
				IntegerNumber concreteEnd = (IntegerNumber) reasoner
						.extractNumber(endIndex);

				if (concreteStart != null && concreteEnd != null) {
					int startInt = concreteStart.intValue();
					int endInt = concreteEnd.intValue();
					LinkedList<SymbolicExpression> valueList = new LinkedList<SymbolicExpression>();

					for (int i = startInt; i < endInt; i++)
						valueList.add(universe.arrayRead(array,
								universe.integer(i)));
					return universe.array(elementType, valueList);
				}
			}
		}
		throw new CIVLInternalException("Unable to extract sub-array", source);
	}

	@Override
	public ReferenceExpression getSymRef(SymbolicExpression pointer) {
		SymbolicExpression result = universe.tupleRead(pointer, twoObj);

		assert result instanceof ReferenceExpression;
		return (ReferenceExpression) result;
	}

	@Override
	public int getVariableId(CIVLSource source, SymbolicExpression pointer) {
		return extractIntField(source, pointer, oneObj);
	}

	// @Override
	// public void setExecutor(Executor executor) {
	// this.executor = executor;
	// }

	@Override
	public SymbolicExpression heapValue(CIVLSource source, State state,
			SymbolicExpression scopeValue)
			throws UnsatisfiablePathConditionException {
		int dyScopeID = modelFactory.getScopeId(source, scopeValue);

		if (dyScopeID < 0) {
			logSimpleError(source, state, ErrorKind.DEREFERENCE,
					"Attempt to dereference pointer into scope which has been removed from state");
			throw new UnsatisfiablePathConditionException();
		} else {
			DynamicScope dyScope = state.getScope(dyScopeID);
			Variable heapVariable = dyScope.lexicalScope().variable("__heap");
			SymbolicExpression heapValue;

			if (heapVariable == null) {
				logSimpleError(source, state, ErrorKind.MEMORY_LEAK,
						"Attempt to dereference pointer into a heap that never exists");
				throw new UnsatisfiablePathConditionException();
			}

			heapValue = dyScope.getValue(heapVariable.vid());
			if (heapValue.equals(universe.nullExpression()))
				heapValue = this.initialHeapValue();
			return heapValue;
		}
	}

	@Override
	public SymbolicExpression heapPointer(CIVLSource source, State state,
			SymbolicExpression scopeValue)
			throws UnsatisfiablePathConditionException {
		ReferenceExpression symRef = (ReferenceExpression) universe
				.canonic(universe.identityReference());
		int dyScopeID = modelFactory.getScopeId(source, scopeValue);

		if (dyScopeID < 0) {
			logSimpleError(source, state, ErrorKind.MEMORY_LEAK,
					"Attempt to access the heap of the scope that has been removed from state");
			throw new UnsatisfiablePathConditionException();
		} else {
			DynamicScope dyScope = state.getScope(dyScopeID);
			Variable heapVariable = dyScope.lexicalScope().variable("__heap");

			if (heapVariable == null) {
				logSimpleError(source, state, ErrorKind.MEMORY_LEAK,
						"Attempt to access a heap that never exists");
				throw new UnsatisfiablePathConditionException();
			}
			return makePointer(dyScopeID, heapVariable.vid(), symRef);
		}
	}

	// @Override
	// public void setExecutor(Executor executor) {
	// this.executor = executor;
	// }

	@Override
	public SymbolicExpression initialHeapValue() {
		return modelFactory.heapType().getInitialValue();
	}

	@Override
	public boolean isProcInCommWithRank(SymbolicExpression comm, int pid,
			int rank) {
		SymbolicExpression procMatrix = this.universe.tupleRead(comm,
				universe.intObject(1));
		SymbolicExpression procQueue = this.universe.arrayRead(procMatrix,
				universe.integer(rank));
		int procRowLength = this.extractInt(
				null,
				(NumericExpression) universe.tupleRead(procQueue,
						universe.intObject(0)));
		SymbolicExpression procRow = universe.tupleRead(procQueue,
				universe.intObject(1));

		for (int j = 0; j < procRowLength; j++) {
			SymbolicExpression proc = universe.arrayRead(procRow,
					universe.integer(j));
			int procId = this.modelFactory.getProcessId(null, proc);

			if (procId == pid)
				return true;
		}
		return false;
	}

	@Override
	public int joinedIDofWait(State state, ProcessState p, WaitStatement wait) {
		Evaluation eval;
		try {
			eval = evaluate(state, p.getPid(), wait.process());
			SymbolicExpression procVal = eval.value;

			return modelFactory.getProcessId(wait.process().getSource(),
					procVal);
		} catch (UnsatisfiablePathConditionException e) {
		}
		return -1;
	}

	@Override
	public State logError(CIVLSource source, State state,
			BooleanExpression claim, ResultType resultType,
			ErrorKind errorKind, String message)
			throws UnsatisfiablePathConditionException {
		BooleanExpression pc = state.getPathCondition(), newPc;
		BooleanExpression npc = universe.not(pc);
		ValidityResult validityResult = trueReasoner.valid(npc);
		ResultType nsat = validityResult.getResultType();
		Certainty certainty;
		CIVLStateException error;

		// performance! need to cache the satisfiability of each pc somewhere
		// negation is slow
		// maybe add "nsat" to Reasoner.
		if (nsat == ResultType.YES)
			// no error to report---an infeasible path
			throw new UnsatisfiablePathConditionException();
		if (nsat == ResultType.MAYBE)
			certainty = Certainty.MAYBE;
		else { // pc is definitely satisfiable
			certainty = null;
			if (resultType == ResultType.NO) {
				// need something satisfying PC and not claim...
				if (solve) {
					ValidityResult claimResult = trueReasoner
							.validOrModel(universe.or(npc, claim));

					if (claimResult.getResultType() == ResultType.NO) {
						Map<SymbolicConstant, SymbolicExpression> model = ((ModelResult) claimResult)
								.getModel();

						if (model != null) {
							certainty = Certainty.CONCRETE;
							message += "\nCounterexample:\n" + model + "\n";
						}
					}
				}
				if (certainty == null)
					certainty = Certainty.PROVEABLE;
			} else {
				certainty = Certainty.MAYBE;
			}
		}
		error = new CIVLStateException(errorKind, certainty, message, state,
				source);
		reportError(error);
		newPc = universe.and(pc, claim);
		// need to check satisfiability again because failure to do so
		// could lead to a SARLException when some subsequent evaluation
		// takes place
		nsat = trueReasoner.valid(universe.not(newPc)).getResultType();
		if (nsat == ResultType.YES)
			throw new UnsatisfiablePathConditionException();
		state = state.setPathCondition(newPc);
		return state;
	}

	/**
	 * Checks whether the path condition is satisfiable and logs an error if it
	 * is (or might be). If the path condition is definitely unsatisfiable,
	 * there is no error to log, and an UnsatisfiablePathConditionException is
	 * thrown.
	 * 
	 * @param source
	 *            source code element used to report the error
	 * @param state
	 *            the current state in which the possible error is detected
	 * @param errorKind
	 *            the kind of error (e.g., DEREFERENCE)
	 * @param message
	 *            the message to include in the error report
	 * @throws UnsatisfiablePathConditionException
	 *             if the path condition is definitely unsatisfiable
	 */
	@Override
	public void logSimpleError(CIVLSource source, State state,
			ErrorKind errorKind, String message)
			throws UnsatisfiablePathConditionException {
		BooleanExpression pc = state.getPathCondition();
		BooleanExpression npc = universe.not(pc);
		ValidityResult validityResult = trueReasoner.valid(npc);
		ResultType nsat = validityResult.getResultType();
		Certainty certainty;
		CIVLStateException error;

		// performance! need to cache the satisfiability of each pc somewhere
		// negation is slow
		// maybe add "nsat" to Reasoner.
		if (nsat == ResultType.YES)
			// no error to report---an infeasible path
			throw new UnsatisfiablePathConditionException();
		if (nsat == ResultType.MAYBE)
			certainty = Certainty.MAYBE;
		else { // pc is definitely satisfiable
			certainty = Certainty.PROVEABLE;
		}
		error = new CIVLStateException(errorKind, certainty, message, state,
				source);
		reportError(error);
	}

	@Override
	public void memoryUnitsOfExpression(State state, int pid,
			Expression expression, Set<SymbolicExpression> memoryUnits)
			throws UnsatisfiablePathConditionException {
		ExpressionKind kind = expression.expressionKind();
		Evaluation eval;

		switch (kind) {
		case ADDRESS_OF:
			AddressOfExpression addressOfExpression = (AddressOfExpression) expression;
			Expression operand = addressOfExpression.operand();

			memoryUnitsOfExpression(state, pid, operand, memoryUnits);
			break;
		case ARRAY_LITERAL:
			Expression[] elements = ((ArrayLiteralExpression) expression)
					.elements();

			for (Expression element : elements) {
				memoryUnitsOfExpression(state, pid, element, memoryUnits);
			}
			break;
		case BINARY:
			BinaryExpression binaryExpression = (BinaryExpression) expression;

			memoryUnitsOfExpression(state, pid, binaryExpression.left(),
					memoryUnits);
			memoryUnitsOfExpression(state, pid, binaryExpression.right(),
					memoryUnits);
			break;
		case BOOLEAN_LITERAL:
			break;
		case CAST:
			CastExpression castExpression = (CastExpression) expression;

			memoryUnitsOfExpression(state, pid, castExpression.getExpression(),
					memoryUnits);
			break;
		case CHAR_LITERAL:
			break;
		case DEREFERENCE:
			DereferenceExpression deferenceExpression = (DereferenceExpression) expression;

			memoryUnitsOfExpression(state, pid, deferenceExpression.pointer(),
					memoryUnits);
			break;

		case DOT:
			DotExpression dotExpression = (DotExpression) expression;

			memoryUnitsOfExpression(state, pid, dotExpression.structOrUnion(),
					memoryUnits);
			break;
		case DYNAMIC_TYPE_OF:
			break;
		case INITIAL_VALUE:
			break;
		case INTEGER_LITERAL:
			break;
		case REAL_LITERAL:
			break;
		case SELF:
			break;
		case SIZEOF_TYPE:
			break;
		case SIZEOF_EXPRESSION:
			SizeofExpressionExpression sizeofExpression = (SizeofExpressionExpression) expression;

			memoryUnitsOfExpression(state, pid, sizeofExpression.getArgument(),
					memoryUnits);
			break;
		case STRUCT_OR_UNION_LITERAL:
			Expression[] fields = ((StructOrUnionLiteralExpression) expression)
					.fields();

			for (Expression field : fields) {
				memoryUnitsOfExpression(state, pid, field, memoryUnits);
			}
			break;
		case SUBSCRIPT:
			SubscriptExpression subscriptExpression = (SubscriptExpression) expression;

			memoryUnitsOfExpression(state, pid, subscriptExpression.array(),
					memoryUnits);
			memoryUnitsOfExpression(state, pid, subscriptExpression.index(),
					memoryUnits);
			break;
		case UNARY:
			UnaryExpression unaryExpression = (UnaryExpression) expression;

			memoryUnitsOfExpression(state, pid, unaryExpression.operand(),
					memoryUnits);
			break;
		case UNDEFINED_PROC:
			break;
		case VARIABLE:
			Variable variable = ((VariableExpression) expression).variable();
			int sid,
			vid;
			CIVLType type;

			try {
				sid = state.getScopeId(pid, variable);
				vid = variable.vid();
				type = variable.type();
			} catch (IllegalArgumentException ex) {
				break;
			}
			// if (!variable.name().name().equals(
			// modelFactory.atomicLockVariableExpression().variable()
			// .name().name())) {
			// atomic_enter statement is always considered as dependent with all
			// processes since it accesses the global variable __atomic_lock_var
			if (!variable.isConst() && !type.isHandleObjectType()) {
				eval = new Evaluation(state, makePointer(sid, vid,
						identityReference));
				memoryUnits.addAll(pointersInExpression(eval.value, state));
			}
			// }
			break;
		case ABSTRACT_FUNCTION_CALL:
			for (Expression arg : ((AbstractFunctionCallExpression) expression)
					.arguments()) {
				memoryUnitsOfExpression(state, pid, arg, memoryUnits);
			}
			break;
		case WAIT_GUARD:
			break;
		case QUANTIFIER:
			break;
		case SYSTEM_GUARD:
			break;
		case HERE_OR_ROOT:
			break;
		case FUNCTION_POINTER:
			break;
		default:
			throw new CIVLUnimplementedFeatureException("Expression kind: "
					+ kind, expression.getSource());
		}
	}

	@Override
	public Set<SymbolicExpression> memoryUnitsOfVariable(
			SymbolicExpression variableValue, int dyScopeID, int vid,
			State state) {
		Evaluation eval = new Evaluation(state, makePointer(dyScopeID, vid,
				identityReference));

		return pointersInExpression(eval.value, state);
	}

	@Override
	public ModelFactory modelFactory() {
		return modelFactory;
	}

	@Override
	public Set<Integer> processesOfSameRankInComm(SymbolicExpression comm,
			int pid, int rank) {
		return new HashSet<Integer>();
		// SymbolicExpression procMatrix = this.universe.tupleRead(comm,
		// universe.intObject(1));
		// SymbolicExpression procQueue = this.universe.arrayRead(procMatrix,
		// universe.integer(rank));
		// int procRowLength = this.extractInt(
		// null,
		// (NumericExpression) universe.tupleRead(procQueue,
		// universe.intObject(0)));
		// SymbolicExpression procRow = universe.tupleRead(procQueue,
		// universe.intObject(1));
		// Set<Integer> pidsInComm = new LinkedHashSet<>();
		//
		// for (int j = 0; j < procRowLength; j++) {
		// SymbolicExpression proc = universe.arrayRead(procRow,
		// universe.integer(j));
		// int procId = this.modelFactory.getProcessId(null, proc);
		//
		// pidsInComm.add(procId);
		// }
		// return pidsInComm;
	}

	@Override
	public SymbolicExpression parentPointer(CIVLSource source,
			SymbolicExpression pointer) {
		ReferenceExpression symRef = getSymRef(pointer);

		if (symRef instanceof NTReferenceExpression)
			return setSymRef(pointer,
					((NTReferenceExpression) symRef).getParent());
		throw new CIVLInternalException("Expected non-trivial pointer: "
				+ pointer, source);
	}

	@Override
	public Evaluation reference(State state, int pid, LHSExpression operand)
			throws UnsatisfiablePathConditionException {
		Evaluation result;

		if (operand instanceof VariableExpression) {
			Variable variable = ((VariableExpression) operand).variable();
			int sid = state.getScopeId(pid, variable);
			int vid = variable.vid();

			result = new Evaluation(state, makePointer(sid, vid,
					identityReference));
		} else if (operand instanceof SubscriptExpression) {
			Evaluation refEval = reference(state, pid,
					((SubscriptExpression) operand).array());
			SymbolicExpression arrayPointer = refEval.value;
			ReferenceExpression oldSymRef = getSymRef(arrayPointer);
			NumericExpression index;
			ReferenceExpression newSymRef;

			result = evaluate(refEval.state, pid,
					((SubscriptExpression) operand).index());
			index = (NumericExpression) result.value;
			newSymRef = universe.arrayElementReference(oldSymRef, index);
			result.value = setSymRef(arrayPointer, newSymRef);
		} else if (operand instanceof DereferenceExpression) {
			result = evaluate(state, pid,
					((DereferenceExpression) operand).pointer());
		} else if (operand instanceof DotExpression) {
			DotExpression dot = (DotExpression) operand;
			int index = dot.fieldIndex();

			if (dot.isStruct()) {
				Evaluation eval = reference(state, pid,
						(LHSExpression) dot.structOrUnion());
				SymbolicExpression structPointer = eval.value;
				ReferenceExpression oldSymRef = getSymRef(structPointer);
				ReferenceExpression newSymRef = universe
						.tupleComponentReference(oldSymRef,
								universe.intObject(index));

				eval.value = setSymRef(structPointer, newSymRef);
				result = eval;
			} else {
				return reference(state, pid,
						(LHSExpression) dot.structOrUnion());
			}
		} else
			throw new CIVLInternalException("Unknown kind of LHSExpression",
					operand);
		return result;
	}

	@Override
	public SymbolicType referencedType(CIVLSource source, State state,
			SymbolicExpression pointer) {
		int sid = getScopeId(source, pointer);
		int vid = getVariableId(source, pointer);
		ReferenceExpression symRef = getSymRef(pointer);
		SymbolicExpression variableValue = state.getScope(sid).getValue(vid);
		SymbolicType variableType = variableValue.type();
		SymbolicType result = universe.referencedType(variableType, symRef);

		return result;
	}

	@Override
	public void reportError(CIVLExecutionException err) {
		try {
			log.report(new CIVLLogEntry(config, err));
		} catch (FileNotFoundException e) {
			throw new CIVLException(e.toString(), err.getSource());
		}
	}

	// @Override
	// public void setExecutor(Executor executor) {
	// this.executor = executor;
	// }

	@Override
	public void setEnabler(Enabler enabler) {
		this.enabler = enabler;
	}

	@Override
	public void setSolve(boolean value) {
		this.solve = value;
	}

	@Override
	public SymbolicExpression setSymRef(SymbolicExpression pointer,
			ReferenceExpression symRef) {
		return universe.tupleWrite(pointer, twoObj, symRef);
	}

	@Override
	public NumericExpression sizeof(CIVLSource source, SymbolicType type) {
		NumericExpression result = sizeofDynamicMap.get(type);

		if (result == null) {

			if (type.isBoolean())
				result = modelFactory.booleanType().getSizeof();
			else if (type == modelFactory.dynamicSymbolicType())
				result = modelFactory.dynamicType().getSizeof();
			else if (type.isInteger())
				result = modelFactory.integerType().getSizeof();
			else if (type == modelFactory.processSymbolicType())
				result = modelFactory.processType().getSizeof();
			else if (type.isReal())
				result = modelFactory.realType().getSizeof();
			else if (type == modelFactory.scopeSymbolicType())
				result = modelFactory.scopeType().getSizeof();
			else if (type instanceof SymbolicCompleteArrayType) {
				SymbolicCompleteArrayType arrayType = (SymbolicCompleteArrayType) type;

				result = sizeof(source, arrayType.elementType());
				result = universe.multiply(arrayType.extent(),
						(NumericExpression) result);
			} else if (type instanceof SymbolicArrayType) {
				throw new CIVLInternalException(
						"sizeof applied to incomplete array type", source);
			} else {
				// wrap the type in an expression of type dynamicTYpe
				SymbolicExpression typeExpr = expressionOfType(type);

				result = (NumericExpression) universe.apply(sizeofFunction,
						new Singleton<SymbolicExpression>(typeExpr));
			}
			sizeofDynamicMap.put(type, result);
		}
		return result;
	}

	public StateFactory stateFactory() {
		return stateFactory;
	}

	public SymbolicUniverse universe() {
		return universe;
	}

}
