package edu.udel.cis.vsl.civl.library.civlc;

import java.io.PrintStream;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.udel.cis.vsl.civl.err.CIVLInternalException;
import edu.udel.cis.vsl.civl.err.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.err.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.kripke.Enabler;
import edu.udel.cis.vsl.civl.library.CommonLibraryEnabler;
import edu.udel.cis.vsl.civl.library.IF.LibraryEnabler;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.semantics.Evaluation;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicSequence;

/**
 * Implementation of the enabler-related logics for system functions declared
 * civlc.h.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class LibcivlcEnabler extends CommonLibraryEnabler implements
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
	public LibcivlcEnabler(Enabler primaryEnabler, PrintStream output,
			ModelFactory modelFactory) {
		super(primaryEnabler, output, modelFactory);
	}

	/* ************************ Methods from Library *********************** */

	@Override
	public String name() {
		// TODO Auto-generated method stub
		return "civlc";
	}

	/* ********************* Methods from LibraryEnabler ******************* */

	@Override
	public Set<Integer> ampleSet(State state, int pid,
			CallOrSpawnStatement statement,
			Map<Integer, Map<SymbolicExpression, Boolean>> reachableMemUnitsMap) {
		Identifier name;
		CallOrSpawnStatement call;

		if (!(statement instanceof CallOrSpawnStatement)) {
			throw new CIVLInternalException("Unsupported statement for civlc",
					statement);
		}
		call = (CallOrSpawnStatement) statement;
		name = call.function().name();

		switch (name.name()) {
		case "$comm_enqueue":
		case "$comm_dequeue":
		case "$barrier_enter":
			return ampleSetWork(state, pid, call, reachableMemUnitsMap);
		default:
			return super.ampleSet(state, pid, statement, reachableMemUnitsMap);
		}
	}

	@Override
	public Evaluation evaluateGuard(CIVLSource source, State state, int pid,
			String function, List<Expression> arguments) {
		SymbolicExpression[] argumentValues;
		int numArgs;
		BooleanExpression guard;

		numArgs = arguments.size();
		argumentValues = new SymbolicExpression[numArgs];
		for (int i = 0; i < numArgs; i++) {
			Evaluation eval = null;

			try {
				eval = evaluator.evaluate(state, pid, arguments.get(i));
			} catch (UnsatisfiablePathConditionException e) {
				// the error that caused the unsatifiable path condition should
				// already have been reported.
				return new Evaluation(state, universe.falseExpression());
			}
			argumentValues[i] = eval.value;
			state = eval.state;
		}

		switch (function) {
		case "$comm_dequeue":
			try {
				guard = getDequeueGuard(state, pid, arguments, argumentValues);
			} catch (UnsatisfiablePathConditionException e) {
				// the error that caused the unsatifiable path condition should
				// already have been reported.
				return new Evaluation(state, universe.falseExpression());
			}
			break;
		case "$wait":
			guard = getWaitGuard(state, pid, arguments, argumentValues);
			break;
		case "$barrier_exit":
			try {
				guard = getBarrierExitGuard(state, pid, arguments,
						argumentValues);
			} catch (UnsatisfiablePathConditionException e) {
				// the error that caused the unsatifiable path condition should
				// already have been reported.
				return new Evaluation(state, universe.falseExpression());
			}
			break;
		case "$bundle_pack":
		case "$bundle_size":
		case "$bundle_unpack":
		case "$barrier_create":
		case "$barrier_enter":
		case "$barrier_destroy":
		case "$gbarrier_create":
		case "$gbarrier_destroy":
		case "$comm_create":
		case "$comm_defined":
		case "$comm_enqueue":
		case "$comm_probe":
		case "$comm_seek":
		case "$comm_size":
		case "$exit":
		case "$comm_destroy":
		case "$gcomm_destroy":
		case "$free":
		case "$gcomm_create2":
		case "$gcomm_defined":
		case "$proc_defined":
			// case "$proc_null":
		case "$scope_parent":
		case "$scope_defined":
			guard = universe.trueExpression();
			break;
		default:
			throw new CIVLInternalException("Unknown civlc function: "
					+ function, source);
		}
		return new Evaluation(state, guard);
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
	 */
	private Set<Integer> ampleSetWork(State state, int pid,
			CallOrSpawnStatement call,
			Map<Integer, Map<SymbolicExpression, Boolean>> reachableMemUnitsMap) {
		int numArgs;
		numArgs = call.arguments().size();
		Expression[] arguments;
		SymbolicExpression[] argumentValues;
		String function = call.function().name().name();
		CIVLSource source = call.getSource();
		Set<Integer> ampleSet = new HashSet<>();

		arguments = new Expression[numArgs];
		argumentValues = new SymbolicExpression[numArgs];
		for (int i = 0; i < numArgs; i++) {
			Evaluation eval = null;

			arguments[i] = call.arguments().get(i);
			try {
				eval = evaluator.evaluate(state, pid, arguments[i]);
			} catch (UnsatisfiablePathConditionException e) {
				return new HashSet<>();
			}
			argumentValues[i] = eval.value;
			state = eval.state;
		}

		switch (function) {
		case "$barrier_enter":
			try {
				SymbolicExpression barrier = evaluator.evaluate(state, pid, arguments[0]).value;
				SymbolicExpression barrierObj = evaluator.dereference(source, state, barrier).value;
				SymbolicExpression gbarrier = universe.tupleRead(barrierObj, oneObject);
				SymbolicExpression gbarrierObj = evaluator.dereference(source, state, gbarrier).value;
				SymbolicExpression procMapArray = universe.tupleRead(gbarrierObj, oneObject);
				SymbolicSequence<?> procMapElements = (SymbolicSequence<?>) procMapArray.argument(0);
				int count = procMapElements.size();
				
				for(int i = 0; i < count; i++){
					SymbolicExpression processValue = procMapElements.get(i);
					int otherPid = modelFactory.getProcessId(source, processValue);
					
					if(pid != otherPid){
						ampleSet.add(otherPid);
					}
				}
			} catch (UnsatisfiablePathConditionException e1) {
				// TODO Auto-generated catch block
				e1.printStackTrace();
			}
			return ampleSet;
		case "$comm_dequeue":
		case "$comm_enqueue":
			Set<SymbolicExpression> handleObjMemUnits = new HashSet<>();

			try {
				evaluator.memoryUnitsOfExpression(state, pid, arguments[0],
						handleObjMemUnits);
			} catch (UnsatisfiablePathConditionException e) {
				handleObjMemUnits.add(argumentValues[0]);
			}
			for (SymbolicExpression memUnit : handleObjMemUnits) {
				for (int otherPid : reachableMemUnitsMap.keySet()) {
					if (otherPid == pid || ampleSet.contains(otherPid))
						continue;
					else if (reachableMemUnitsMap.get(otherPid).containsKey(
							memUnit)) {
						ampleSet.add(otherPid);
					}
				}
			}
			return ampleSet;
		default:
			throw new CIVLInternalException("Unreachable" + function, source);
		}
	}

	/**
	 * Computes the guard of $barrier_exit($barrier), i.e., when the
	 * corresponding cell of in_barrier array in $gbarrier is false.
	 * 
	 * @param state
	 * @param pid
	 * @param arguments
	 * @param argumentValues
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private BooleanExpression getBarrierExitGuard(State state, int pid,
			List<Expression> arguments, SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		CIVLSource source = arguments.get(0).getSource();
		SymbolicExpression barrier = argumentValues[0];
		NumericExpression myPlace;
		SymbolicExpression barrierObj;
		SymbolicExpression gbarrier;
		SymbolicExpression gbarrierObj;
		Evaluation eval = evaluator.dereference(source, state, barrier);
		SymbolicExpression inBarrierArray;
		SymbolicExpression meInBarrier;

		state = eval.state;
		barrierObj = eval.value;
		myPlace = (NumericExpression) universe
				.tupleRead(barrierObj, zeroObject);
		gbarrier = universe.tupleRead(barrierObj, oneObject);
		eval = evaluator.dereference(source, state, gbarrier);
		state = eval.state;
		gbarrierObj = eval.value;
		inBarrierArray = universe.tupleRead(gbarrierObj, twoObject);
		meInBarrier = universe.arrayRead(inBarrierArray, myPlace);
		if (meInBarrier.isTrue())
			return universe.falseExpression();
		return universe.trueExpression();
	}

	/**
	 * Computes the guard of $comm_dequeue().
	 * 
	 * @param state
	 * @param pid
	 * @param arguments
	 *            $comm, source, tag
	 * @param argumentValues
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private BooleanExpression getDequeueGuard(State state, int pid,
			List<Expression> arguments, SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression commHandle = argumentValues[0];
		SymbolicExpression source = argumentValues[1];
		SymbolicExpression tag = argumentValues[2];
		SymbolicExpression comm;
		SymbolicExpression gcommHandle;
		SymbolicExpression gcomm;
		SymbolicExpression dest;
		SymbolicExpression newMessage;
		CIVLSource civlsource = arguments.get(0).getSource();
		boolean enabled = false;
		Evaluation eval;

		eval = evaluator.dereference(civlsource, state, commHandle);
		state = eval.state;
		comm = eval.value;
		gcommHandle = universe.tupleRead(comm, oneObject);
		eval = evaluator.dereference(civlsource, state, gcommHandle);
		state = eval.state;
		gcomm = eval.value;
		dest = universe.tupleRead(comm, zeroObject);
		newMessage = this.getMatchedMessageFromGcomm(pid, gcomm, source, dest,
				tag, civlsource);
		if (newMessage != null)
			enabled = true;
		return universe.bool(enabled);
	}

	/**
	 * Computes matched message in the communicator.
	 * 
	 * @param pid
	 *            The process ID.
	 * @param gcomm
	 *            The dynamic representation of the communicator.
	 * @param source
	 *            The expected source.
	 * @param dest
	 *            The expected destination.
	 * @param tag
	 *            The expected tag.
	 * @param civlsource
	 *            The source code element for error report.
	 * @return The matched message, NULL if no matched message found.
	 * @throws UnsatisfiablePathConditionException
	 */
	private SymbolicExpression getMatchedMessageFromGcomm(int pid,
			SymbolicExpression gcomm, SymbolicExpression source,
			SymbolicExpression dest, SymbolicExpression tag,
			CIVLSource civlsource) throws UnsatisfiablePathConditionException {
		SymbolicExpression buf;
		SymbolicExpression bufRow;
		SymbolicExpression queue;
		SymbolicExpression queueLength;
		SymbolicExpression messages = null;
		SymbolicExpression message = null;
		int int_source = evaluator.extractInt(civlsource,
				(NumericExpression) source);
		int int_tag = evaluator.extractInt(civlsource, (NumericExpression) tag);
		int int_queueLength;

		buf = universe.tupleRead(gcomm, universe.intObject(2));
		// specific source and tag
		if (int_source >= 0 && int_tag >= 0) {
			bufRow = universe.arrayRead(buf, (NumericExpression) source);
			queue = universe.arrayRead(bufRow, (NumericExpression) dest);
			messages = universe.tupleRead(queue, oneObject);
			queueLength = universe.tupleRead(queue, zeroObject);
			int_queueLength = evaluator.extractInt(civlsource,
					(NumericExpression) queueLength);
			for (int i = 0; i < int_queueLength; i++) {
				message = universe.arrayRead(messages, universe.integer(i));
				if (universe.tupleRead(message, universe.intObject(2)).equals(
						tag))
					break;
				else
					message = null;
			}
		} else if (int_source >= 0 && int_tag == -2) {
			bufRow = universe.arrayRead(buf, (NumericExpression) source);
			queue = universe.arrayRead(bufRow, (NumericExpression) dest);
			messages = universe.tupleRead(queue, oneObject);
			queueLength = universe.tupleRead(queue, zeroObject);
			int_queueLength = evaluator.extractInt(civlsource,
					(NumericExpression) queueLength);
			if (int_queueLength > 0)
				message = universe.arrayRead(messages, zero);
			else
				message = null;
		} else {
			throw new CIVLUnimplementedFeatureException("$COMM_ANY_SOURCE");
		}
		return message;
	}

	/**
	 * Computes the guard of $wait.
	 * 
	 * @param state
	 * @param pid
	 * @param arguments
	 * @param argumentValues
	 * @return
	 */
	private BooleanExpression getWaitGuard(State state, int pid,
			List<Expression> arguments, SymbolicExpression[] argumentValues) {
		SymbolicExpression joinProcess = argumentValues[0];
		BooleanExpression guard;
		int pidValue;
		Expression joinProcessExpr = arguments.get(0);

		pidValue = modelFactory.getProcessId(joinProcessExpr.getSource(),
				joinProcess);
		if (!state.getProcessState(pidValue).hasEmptyStack())
			guard = universe.falseExpression();
		else
			guard = universe.trueExpression();
		return guard;
	}

}
