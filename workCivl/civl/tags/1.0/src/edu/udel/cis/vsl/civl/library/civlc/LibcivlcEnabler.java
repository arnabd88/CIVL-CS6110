package edu.udel.cis.vsl.civl.library.civlc;

import java.math.BigInteger;
import java.util.BitSet;
import java.util.LinkedList;
import java.util.List;

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
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;

/**
 * Implementation of the enabler-related logics for system functions declared
 * civlc.h.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class LibcivlcEnabler extends BaseLibraryEnabler implements
		LibraryEnabler {
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

		switch (functionName) {
		case "$choose_int":
			eval = evaluator.evaluate(state.setPathCondition(pathCondition),
					pid, arguments.get(0));
			IntegerNumber upperNumber = (IntegerNumber) universe.reasoner(
					eval.state.getPathCondition()).extractNumber(
					(NumericExpression) eval.value);
			int upper;

			// TODO: is it can be solved by symbolic execution ?
			if (upperNumber == null) {
				throw new CIVLExecutionException(ErrorKind.INTERNAL,
						Certainty.NONE, process,
						"Argument to $choose_int not concrete: " + eval.value,
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
						procPointer, false);
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
}
