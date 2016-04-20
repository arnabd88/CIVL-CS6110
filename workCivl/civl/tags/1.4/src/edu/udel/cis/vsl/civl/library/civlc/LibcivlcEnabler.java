package edu.udel.cis.vsl.civl.library.civlc;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.BitSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.kripke.IF.Enabler;
import edu.udel.cis.vsl.civl.kripke.IF.LibraryEnabler;
import edu.udel.cis.vsl.civl.kripke.IF.LibraryEnablerLoader;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryEnabler;
import edu.udel.cis.vsl.civl.log.IF.CIVLExecutionException;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.Certainty;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression.BINARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.InitialValueExpression;
import edu.udel.cis.vsl.civl.model.IF.statement.AssignStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.Semantics;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.semantics.IF.Transition;
import edu.udel.cis.vsl.civl.semantics.IF.Transition.AtomicLockAction;
import edu.udel.cis.vsl.civl.state.IF.MemoryUnitSet;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicCollection;

/**
 * Implementation of the enabler-related logics for system functions declared
 * civlc.h.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class LibcivlcEnabler extends BaseLibraryEnabler implements
		LibraryEnabler {

	private final static int ELABORATE_UPPER_BOUND = 100;

	/* **************************** Constructors *************************** */
	/**
	 * Creates a new instance of the library enabler for civlc.h.
	 * 
	 * @param primaryEnabler
	 *            The enabler for normal CIVL execution.
	 * @param output
	 *            The output stream to be used in the enabler.
	 * @param modelFactory
	 *            The model factory of the system.
	 */
	public LibcivlcEnabler(String name, Enabler primaryEnabler,
			Evaluator evaluator, ModelFactory modelFactory,
			SymbolicUtility symbolicUtil, SymbolicAnalyzer symbolicAnalyzer,
			CIVLConfiguration civlConfig,
			LibraryEnablerLoader libEnablerLoader,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, primaryEnabler, evaluator, modelFactory, symbolicUtil,
				symbolicAnalyzer, civlConfig, libEnablerLoader,
				libEvaluatorLoader);
	}

	/* ********************* Methods from LibraryEnabler ******************* */

	@Override
	public BitSet ampleSet(State state, int pid, CallOrSpawnStatement call,
			MemoryUnitSet[] reachablePtrWritableMap,
			MemoryUnitSet[] reachablePtrReadonlyMap,
			MemoryUnitSet[] reachableNonPtrWritableMap,
			MemoryUnitSet[] reachableNonPtrReadonlyMap)
			throws UnsatisfiablePathConditionException {
		return this.ampleSetWork(state, pid, call);
	}

	@Override
	public List<Transition> enabledTransitions(State state,
			CallOrSpawnStatement call, BooleanExpression pathCondition,
			int pid, int processIdentifier, AtomicLockAction atomicLockAction)
			throws UnsatisfiablePathConditionException {
		String functionName = call.function().name().name();
		AssignStatement assignmentCall;
		List<Expression> arguments = call.arguments();
		List<Transition> localTransitions = new LinkedList<>();
		Evaluation eval;
		String process = "p" + processIdentifier + " (id = " + pid + ")";
		SymbolicExpression[] argumentValues = new SymbolicExpression[arguments
				.size()];

		for (int i = 0; i < arguments.size(); i++) {
			eval = evaluator.evaluate(state.setPathCondition(pathCondition),
					pid, arguments.get(i));
			state = eval.state;
			argumentValues[i] = eval.value;
		}
		switch (functionName) {
		case "$choose_int":
			IntegerNumber upperNumber = (IntegerNumber) universe.reasoner(
					state.getPathCondition()).extractNumber(
					(NumericExpression) argumentValues[0]);
			int upper;

			// TODO: is it can be solved by symbolic execution ?
			if (upperNumber == null) {
				throw new CIVLExecutionException(ErrorKind.INTERNAL,
						Certainty.NONE, process,
						"Argument to $choose_int not concrete: "
								+ argumentValues[0],
						symbolicAnalyzer.stateInformation(state), arguments
								.get(0).getSource());
			}
			upper = upperNumber.intValue();
			for (int i = 0; i < upper; i++) {
				Expression singleChoice = modelFactory
						.integerLiteralExpression(arguments.get(0).getSource(),
								BigInteger.valueOf(i));

				assignmentCall = modelFactory.assignStatement(arguments.get(0)
						.getSource(), call.source(), call.lhs(), singleChoice,
						(call.lhs() instanceof InitialValueExpression));
				assignmentCall.setTargetTemp(call.target());
				assignmentCall.setTarget(call.target());
				localTransitions.add(Semantics.newTransition(pathCondition,
						pid, processIdentifier, assignmentCall,
						atomicLockAction));
			}
			break;
		case "$elaborate":
			return this.elaborateIntWorker(state, pid, processIdentifier, call,
					call.getSource(), arguments, argumentValues,
					atomicLockAction);
		default:
			return super.enabledTransitions(state, call, pathCondition, pid,
					processIdentifier, atomicLockAction);
		}
		return localTransitions;
	}

	/* *************************** Private Methods ************************* */

	/**
	 * Computes the ample set process ID's from a system function call.
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the process that the system function call belongs
	 *            to.
	 * @param call
	 *            The system function call statement.
	 * @param reachableMemUnitsMap
	 *            The map of reachable memory units of all active processes.
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private BitSet ampleSetWork(State state, int pid, CallOrSpawnStatement call)
			throws UnsatisfiablePathConditionException {
		int numArgs;
		numArgs = call.arguments().size();
		Expression[] arguments;
		SymbolicExpression[] argumentValues;
		String function = call.function().name().name();

		arguments = new Expression[numArgs];
		argumentValues = new SymbolicExpression[numArgs];
		for (int i = 0; i < numArgs; i++) {
			Evaluation eval = null;

			arguments[i] = call.arguments().get(i);
			try {
				eval = evaluator.evaluate(state, pid, arguments[i]);
			} catch (UnsatisfiablePathConditionException e) {
				return new BitSet(0);
			}
			argumentValues[i] = eval.value;
			state = eval.state;
		}

		switch (function) {
		case "$wait":
			return ampleSetOfWait(state, pid, arguments, argumentValues);
		case "$waitall":
			return ampleSetOfWaitall(state, pid, arguments, argumentValues);
		default:
			return super.ampleSet(state, pid, call, null, null, null, null);
		}
	}

	private BitSet ampleSetOfWait(State state, int pid, Expression[] arguments,
			SymbolicExpression[] argumentValues) {
		SymbolicExpression joinProc = argumentValues[0];
		int joinPid = modelFactory.getProcessId(arguments[0].getSource(),
				joinProc);
		BitSet ampleSet = new BitSet();

		if (modelFactory.isPocessIdDefined(joinPid)
				&& !modelFactory.isProcNull(arguments[0].getSource(), joinProc)) {
			ampleSet.set(joinPid);
		}
		return ampleSet;
	}

	private BitSet ampleSetOfWaitall(State state, int pid,
			Expression[] arguments, SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression procsPointer = argumentValues[0];
		SymbolicExpression numOfProcs = argumentValues[1];
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		IntegerNumber number_nprocs = (IntegerNumber) reasoner
				.extractNumber((NumericExpression) numOfProcs);
		String process = state.getProcessState(pid).name() + "(id=" + pid + ")";
		BitSet ampleSet = new BitSet();

		if (number_nprocs == null) {
			CIVLExecutionException err = new CIVLExecutionException(
					ErrorKind.OTHER, Certainty.PROVEABLE, process,
					"The number of processes for $waitall "
							+ "needs a concrete value.",
					symbolicAnalyzer.stateInformation(state),
					arguments[1].getSource());

			this.evaluator.errorLogger().reportError(err);
			return ampleSet;
		} else {
			int numOfProcs_int = number_nprocs.intValue();
			BinaryExpression pointerAdd;
			CIVLSource procsSource = arguments[0].getSource();
			Evaluation eval;

			for (int i = 0; i < numOfProcs_int; i++) {
				Expression offSet = modelFactory.integerLiteralExpression(
						procsSource, BigInteger.valueOf(i));
				NumericExpression offSetV = universe.integer(i);
				SymbolicExpression procPointer, proc;
				int pidValue;

				pointerAdd = modelFactory.binaryExpression(procsSource,
						BINARY_OPERATOR.POINTER_ADD, arguments[0], offSet);
				eval = evaluator.pointerAdd(state, pid, process, pointerAdd,
						procsPointer, offSetV);
				procPointer = eval.value;
				state = eval.state;
				eval = evaluator.dereference(procsSource, state, process,
						pointerAdd, procPointer, false);
				proc = eval.value;
				state = eval.state;
				pidValue = modelFactory.getProcessId(procsSource, proc);
				if (!modelFactory.isProcessIdNull(pidValue)
						&& modelFactory.isPocessIdDefined(pidValue))
					ampleSet.set(pidValue);
			}
		}
		return ampleSet;
	}

	/**
	 * This methods elaborates all symbolic constants contained in an
	 * expression.
	 * 
	 * @param state
	 * @param pid
	 * @param source
	 * @param arguments
	 * @param argumentValues
	 * @param atomicLockAction
	 * @return
	 */
	private List<Transition> elaborateIntWorker(State state, int pid,
			int processIdentifier, Statement call, CIVLSource source,
			List<Expression> arguments, SymbolicExpression[] argumentValues,
			AtomicLockAction atomicLockAction) {
		Set<SymbolicConstant> symbolicConstants = universe
				.getFreeSymbolicConstants(argumentValues[0]);
		BooleanExpression pathCondition = state.getPathCondition();
		BooleanExpression[] clauses = this.symbolicUtil
				.getConjunctiveClauses(pathCondition);
		Map<SymbolicConstant, Pair<Integer, Integer>> boundsMap;
		ConstantBound[] constantBounds;
		Set<BooleanExpression> concreteValueClauses;
		List<Transition> transitions = new LinkedList<>();
		int index = 0;
		Reasoner reasoner = universe.reasoner(pathCondition);

		if (symbolicConstants.size() < 1) {
			return Arrays.asList((Transition) Semantics.newNoopTransition(
					pathCondition, pid, processIdentifier, null, call, false,
					atomicLockAction));
		}
		state = this.stateFactory.simplify(state);
		boundsMap = extractsUpperBoundAndLowBoundOf(clauses, symbolicConstants);
		if (boundsMap.size() < 1) {
			return Arrays.asList((Transition) Semantics.newNoopTransition(
					pathCondition, pid, processIdentifier, null, call, false,
					atomicLockAction));
		}
		constantBounds = new ConstantBound[boundsMap.size()];
		for (Entry<SymbolicConstant, Pair<Integer, Integer>> constantAndBounds : boundsMap
				.entrySet()) {
			constantBounds[index++] = new ConstantBound(
					constantAndBounds.getKey(),
					constantAndBounds.getValue().left,
					constantAndBounds.getValue().right);
		}
		concreteValueClauses = this.generateConcreteValueClauses(reasoner,
				constantBounds, 0);
		for (BooleanExpression clause : concreteValueClauses) {
			BooleanExpression newPathCondition = (BooleanExpression) universe
					.canonic(universe.and(pathCondition, clause));

			transitions.add(Semantics.newNoopTransition(newPathCondition, pid,
					processIdentifier, clause, call, true, atomicLockAction));
		}
		return transitions;
	}

	private Set<BooleanExpression> generateConcreteValueClauses(
			Reasoner reasoner, ConstantBound[] constantBounds, int start) {
		Set<BooleanExpression> myResult = new LinkedHashSet<>();
		ConstantBound myConstantBound = constantBounds[start];
		Set<BooleanExpression> subfixResult;
		Set<BooleanExpression> result = new LinkedHashSet<>();

		// last constant bound
		int lower = myConstantBound.lower, upper = myConstantBound.upper;
		NumericExpression symbol = (NumericExpression) myConstantBound.constant;
		BooleanExpression newClause;
		boolean upperBoundCluaseNeeded = false;

		if (lower < 0) {
			lower = 0;
			newClause = universe.lessThan(symbol, universe.integer(lower));
			if (!reasoner.isValid(universe.not(newClause)))
				myResult.add(newClause);
		}
		if (upper > lower + ELABORATE_UPPER_BOUND) {
			upper = lower + ELABORATE_UPPER_BOUND;
			upperBoundCluaseNeeded = true;
			newClause = universe.lessThan(universe.integer(upper), symbol);
			if (!reasoner.isValid(universe.not(newClause)))
				myResult.add(newClause);
		}
		for (int value = lower; value <= upper; value++) {
			newClause = universe.equals(symbol, universe.integer(value));
			if (!reasoner.isValid(universe.not(newClause)))
				myResult.add(newClause);
		}
		if (upperBoundCluaseNeeded)
			myResult.add(universe.lessThan(universe.integer(upper), symbol));
		if (start == constantBounds.length - 1)
			return myResult;
		subfixResult = this.generateConcreteValueClauses(reasoner,
				constantBounds, start + 1);
		for (BooleanExpression myClause : myResult) {
			for (BooleanExpression subfixClause : subfixResult) {
				result.add(universe.and(myClause, subfixClause));
			}
		}
		return result;
	}

	private Map<SymbolicConstant, Pair<Integer, Integer>> extractsUpperBoundAndLowBoundOf(
			BooleanExpression[] clauses, Set<SymbolicConstant> symbolicConstants) {
		Map<SymbolicConstant, Pair<Integer, Integer>> result = new LinkedHashMap<>();
		int length = clauses.length;

		for (int i = 0; i < length; i++) {
			BooleanExpression clause = clauses[i];
			SymbolicOperator operator = clause.operator();
			SymbolicConstant symbol;
			boolean isLTE = operator == SymbolicOperator.LESS_THAN_EQUALS, isLT = operator == SymbolicOperator.LESS_THAN;
			SymbolicExpression polynomial;
			Set<SymbolicConstant> symbols;
			Pair<Integer, Integer> mybounds;
			SymbolicOperator polynomialOperator;

			if (!isLTE && !isLT)
				continue;
			if (!this.isZeroConstant((SymbolicExpression) clause.argument(0)))
				continue;
			symbols = universe.getFreeSymbolicConstants(clause);
			if (symbols.size() != 1)
				continue;
			symbol = symbols.iterator().next();
			if (!symbolicConstants.contains(symbol))
				continue;
			mybounds = result.get(symbol);
			if (mybounds == null)
				mybounds = new Pair<>(Integer.MIN_VALUE, Integer.MAX_VALUE);
			polynomial = (SymbolicExpression) clause.argument(1);
			polynomialOperator = polynomial.operator();
			if (polynomialOperator == SymbolicOperator.SYMBOLIC_CONSTANT) {
				// 0 < X or 0<=X TODO check 0 < -X
				int lowerbound = isLTE ? 0 : 1;

				mybounds.left = this.max(mybounds.left, lowerbound);
				result.put(symbol, mybounds);
			} else if (polynomialOperator == SymbolicOperator.ADD) {
				// the polynomial always has the form (-1*X) + N,
				// where N could be a positive or a negative integer
				// symbolPart is X or -1*x
				@SuppressWarnings("unchecked")
				SymbolicCollection<? extends SymbolicExpression> polynomialCollection = (SymbolicCollection<SymbolicExpression>) polynomial
						.argument(0);
				SymbolicExpression symbolPart = null, integerConstant = null;
				boolean symbolPartPositive;
				int integerConstantValue;
				int index = 0;

				for (SymbolicExpression polyElement : polynomialCollection) {
					if (index == 0)
						symbolPart = polyElement;
					else if (index == 1)
						integerConstant = polyElement;
					index++;
				}
				assert symbolPart != null;
				assert integerConstant != null;
				symbolPartPositive = symbolPart.operator() == SymbolicOperator.SYMBOLIC_CONSTANT;
				if (!symbolPartPositive) {
					if (symbolPart.operator() != SymbolicOperator.MULTIPLY)
						continue;
					if (!this
							.isNegativeOneConstant((SymbolicExpression) symbolPart
									.argument(0)))
						continue;
				}
				integerConstantValue = this.symbolicUtil.extractInt(null,
						(NumericExpression) integerConstant);
				if (symbolPartPositive)
					integerConstantValue = 0 - integerConstantValue;
				if (isLT) {
					if (symbolPartPositive)
						integerConstantValue++;
					else
						integerConstantValue--;
				}
				if (symbolPartPositive) {
					// this is the lowerbound
					mybounds.left = this.max(mybounds.left,
							integerConstantValue);
				} else {
					// upper bound
					mybounds.right = this.min(mybounds.right,
							integerConstantValue);
				}
				result.put(symbol, mybounds);
			}
		}
		return result;
	}

	private boolean isNegativeOneConstant(SymbolicExpression expression) {
		if (expression instanceof NumericExpression) {
			return this.symbolicUtil.extractInt(null,
					(NumericExpression) expression) == -1;
		}
		return false;
	}

	private int min(int a, int b) {
		return a <= b ? a : b;
	}

	private int max(int a, int b) {
		return a >= b ? a : b;
	}

	private boolean isZeroConstant(SymbolicExpression expression) {
		if (expression instanceof NumericExpression) {
			Number number = universe
					.extractNumber((NumericExpression) expression);

			return number.isZero();
		}
		return false;
	}
}

class ConstantBound {
	SymbolicConstant constant;
	int lower;
	int upper;

	ConstantBound(SymbolicConstant constant, int lower, int upper) {
		this.constant = constant;
		this.lower = lower;
		this.upper = upper;
	}
}
