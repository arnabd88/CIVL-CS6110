package edu.udel.cis.vsl.civl.library.concurrency;

import java.util.Arrays;
import java.util.LinkedList;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryExecutor;
import edu.udel.cis.vsl.civl.log.IF.CIVLExecutionException;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.Certainty;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;

public class LibconcurrencyExecutor extends BaseLibraryExecutor implements
		LibraryExecutor {

	/* **************************** Constructors *************************** */

	/**
	 * Creates a new instance of the library executor for concurrency.cvh.
	 * 
	 * @param name
	 *            The name of the library, which is concurrency.
	 * @param primaryExecutor
	 *            The executor for normal CIVL execution.
	 * @param modelFactory
	 *            The model factory of the system.
	 * @param symbolicUtil
	 *            The symbolic utility to be used.
	 * @param civlConfig
	 *            The CIVL configuration configured by the user.
	 */
	public LibconcurrencyExecutor(String name, Executor primaryExecutor,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer, CIVLConfiguration civlConfig) {
		super(name, primaryExecutor, modelFactory, symbolicUtil,
				symbolicAnalyzer, civlConfig);
	}

	/* ******************** Methods from LibraryExecutor ******************* */

	@Override
	public State execute(State state, int pid, CallOrSpawnStatement statement)
			throws UnsatisfiablePathConditionException {
		return executeWork(state, pid, statement);
	}

	/* ************************** Private Methods ************************** */

	/**
	 * Executes a system function call, updating the left hand side expression
	 * with the returned value if any.
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the process that the function call belongs to.
	 * @param call
	 *            The function call statement to be executed.
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeWork(State state, int pid, CallOrSpawnStatement call)
			throws UnsatisfiablePathConditionException {
		Identifier name;
		Expression[] arguments;
		SymbolicExpression[] argumentValues;
		LHSExpression lhs;
		int numArgs;
		String process = state.getProcessState(pid).name() + "(id=" + pid + ")";

		numArgs = call.arguments().size();
		name = call.function().name();
		lhs = call.lhs();
		arguments = new Expression[numArgs];
		argumentValues = new SymbolicExpression[numArgs];
		for (int i = 0; i < numArgs; i++) {
			Evaluation eval;

			arguments[i] = call.arguments().get(i);
			eval = evaluator.evaluate(state, pid, arguments[i]);
			argumentValues[i] = eval.value;
			state = eval.state;
		}
		switch (name.name()) {
		case "$barrier_create":
			state = executeBarrierCreate(state, pid, process, lhs, arguments,
					argumentValues, call.getSource());
			break;
		case "$barrier_enter":
			state = executeBarrierEnter(state, pid, process, arguments,
					argumentValues);
			break;
		case "$barrier_exit":
			// does nothing
			break;
		case "$gbarrier_create":
			state = executeGbarrierCreate(state, pid, process, lhs, arguments,
					argumentValues, call.getSource());
			break;
		case "$barrier_destroy":
		case "$gbarrier_destroy":
			state = executeFree(state, pid, process, arguments, argumentValues,
					call.getSource());
			break;
		}
		state = stateFactory.setLocation(state, pid, call.target());
		return state;
	}

	/**
	 * Creates a new local communicator object and returns a handle to it. The
	 * new communicator will be affiliated with the specified global
	 * communicator. This local communicator handle will be used as an argument
	 * in most message-passing functions. The place must be in [0,size-1] and
	 * specifies the place in the global communication universe that will be
	 * occupied by the local communicator. The local communicator handle may be
	 * used by more than one process, but all of those processes will be viewed
	 * as occupying the same place. Only one call to $comm_create may occur for
	 * each gcomm-place pair. The new object will be allocated in the given
	 * scope.
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the process that the function call belongs to.
	 * @param lhs
	 *            The left hand side expression of the call, which is to be
	 *            assigned with the returned value of the function call. If NULL
	 *            then no assignment happens.
	 * @param arguments
	 *            The static representation of the arguments of the function
	 *            call.
	 * @param argumentValues
	 *            The dynamic representation of the arguments of the function
	 *            call.
	 * @param source
	 *            The source code element to be used for error report.
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeBarrierCreate(State state, int pid, String process,
			LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression scope = argumentValues[0];
		Expression scopeExpression = arguments[0];
		SymbolicExpression gbarrier = argumentValues[1];
		SymbolicExpression place = argumentValues[2];
		SymbolicExpression gbarrierObj;
		SymbolicExpression barrierObj;
		SymbolicExpression procMapArray;
		LinkedList<SymbolicExpression> barrierComponents = new LinkedList<>();
		CIVLSource civlsource = arguments[1].getSource();
		CIVLType barrierType = modelFactory.getSystemType(Model.BARRIER_TYPE);
		Evaluation eval;
		int place_num = ((IntegerNumber) universe
				.extractNumber((NumericExpression) place)).intValue();
		int totalPlaces;

		if (place_num < 0) {
			throw new CIVLExecutionException(ErrorKind.OTHER,
					Certainty.CONCRETE, process, "Invalid place " + place_num
							+ " used in $barrier_create().", source);
		}
		eval = this.evaluator.dereference(civlsource, state, process, gbarrier,
				false);
		state = eval.state;
		gbarrierObj = eval.value;
		totalPlaces = ((IntegerNumber) universe
				.extractNumber((NumericExpression) universe.tupleRead(
						gbarrierObj, zeroObject))).intValue();
		if (place_num >= totalPlaces) {
			CIVLExecutionException err = new CIVLExecutionException(
					ErrorKind.OTHER,
					Certainty.CONCRETE,
					process,
					"Place "
							+ place_num
							+ " used in $barrier_create() exceeds the size of the $gbarrier.",
					source);

			this.errorLogger.reportError(err);
		}
		procMapArray = universe.tupleRead(gbarrierObj, oneObject);
		if (!universe.arrayRead(procMapArray, (NumericExpression) place)
				.equals(modelFactory.nullProcessValue())) {
			throw new CIVLExecutionException(ErrorKind.OTHER,
					Certainty.CONCRETE, process,
					"Attempt to create a barrier using an invalid place.",
					source);
		}

		// TODO report an error if the place exceeds the size of the
		// communicator
		procMapArray = universe.arrayWrite(procMapArray,
				(NumericExpression) place, modelFactory.processValue(pid));
		gbarrierObj = universe.tupleWrite(gbarrierObj, oneObject, procMapArray);
		state = this.primaryExecutor.assign(civlsource, state, process,
				gbarrier, gbarrierObj);
		// builds barrier object
		barrierComponents.add(place);
		barrierComponents.add(gbarrier);
		barrierObj = universe.tuple(
				(SymbolicTupleType) barrierType.getDynamicType(universe),
				barrierComponents);
		state = this.primaryExecutor.malloc(civlsource, state, pid, process,
				lhs, scopeExpression, scope, barrierType, barrierObj);
		return state;
	}

	/**
	 * Adds the message to the appropriate message queue in the communication
	 * universe specified by the comm. The source of the message must equal the
	 * place of the comm.
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the process that the function call belongs to.
	 * @param arguments
	 *            The static representation of the arguments of the function
	 *            call.
	 * @param argumentValues
	 *            The dynamic representation of the arguments of the function
	 *            call.
	 * @param source
	 *            The source code element to be used for error report.
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeBarrierEnter(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		CIVLSource civlsource = arguments[0].getSource();
		SymbolicExpression barrier = argumentValues[0];
		SymbolicExpression barrierObj;
		SymbolicExpression gbarrier;
		SymbolicExpression gbarrierObj;
		SymbolicExpression inBarrierArray;
		SymbolicExpression nprocs;
		NumericExpression myPlace;
		SymbolicExpression numInBarrier;
		Evaluation eval;
		int numInBarrier_int;
		int nprocs_int;

		eval = evaluator
				.dereference(civlsource, state, process, barrier, false);
		state = eval.state;
		barrierObj = eval.value;
		myPlace = (NumericExpression) universe
				.tupleRead(barrierObj, zeroObject);
		gbarrier = universe.tupleRead(barrierObj, oneObject);
		eval = evaluator.dereference(civlsource, state, process, gbarrier,
				false);
		state = eval.state;
		gbarrierObj = eval.value;
		nprocs = universe.tupleRead(gbarrierObj, zeroObject);
		inBarrierArray = universe.tupleRead(gbarrierObj, twoObject);
		numInBarrier = universe.tupleRead(gbarrierObj, threeObject);
		nprocs_int = symbolicUtil.extractInt(civlsource,
				(NumericExpression) nprocs);
		numInBarrier_int = symbolicUtil.extractInt(civlsource,
				(NumericExpression) numInBarrier);
		numInBarrier_int++;
		if (numInBarrier_int == nprocs_int) {
			LinkedList<SymbolicExpression> inBarrierComponents = new LinkedList<>();

			for (int i = 0; i < nprocs_int; i++) {
				inBarrierComponents.add(universe.falseExpression());
			}
			inBarrierArray = universe.array(universe.booleanType(),
					inBarrierComponents);
			numInBarrier = zero;
		} else {
			numInBarrier = universe.integer(numInBarrier_int);
			inBarrierArray = universe.arrayWrite(inBarrierArray, myPlace,
					universe.trueExpression());
		}
		gbarrierObj = universe.tupleWrite(gbarrierObj, this.twoObject,
				inBarrierArray);
		gbarrierObj = universe.tupleWrite(gbarrierObj, this.threeObject,
				numInBarrier);
		state = this.primaryExecutor.assign(civlsource, state, process,
				gbarrier, gbarrierObj);
		return state;
	}

	/**
	 * Creates a new global barrier object and returns a handle to it. The
	 * global barrier will have size number of processes. The global barrier
	 * defines a barrier "universe" and encompasses the status of processes
	 * associated with the barrier. The new object will be allocated in the
	 * given scope.
	 * 
	 * typedef struct __gbarrier__ { int nprocs; _Bool in_barrier[]; //
	 * initialized as all false. int num_in_barrier; // initialized as 0. } *
	 * $gbarrier;
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the process that the function call belongs to.
	 * @param lhs
	 *            The left hand side expression of the call, which is to be
	 *            assigned with the returned value of the function call. If NULL
	 *            then no assignment happens.
	 * @param arguments
	 *            The static representation of the arguments of the function
	 *            call.
	 * @param argumentValues
	 *            The dynamic representation of the arguments of the function
	 *            call.
	 * @param source
	 *            The source code element to be used for error report.
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeGbarrierCreate(State state, int pid, String process,
			LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression gbarrierObj;
		NumericExpression nprocs = (NumericExpression) argumentValues[1];
		SymbolicExpression numInBarrier = universe.integer(0);
		SymbolicExpression scope = argumentValues[0];
		Expression scopeExpression = arguments[0];
		SymbolicExpression procMapArray;
		SymbolicExpression inBarrierArray;
		CIVLType gbarrierType = modelFactory.getSystemType(Model.GBARRIER_TYPE);
		BooleanExpression context = state.getPathCondition();

		inBarrierArray = symbolicUtil
				.newArray(context, nprocs, this.falseValue);
		procMapArray = symbolicUtil.newArray(context, nprocs,
				modelFactory.nullProcessValue());
		gbarrierObj = universe.tuple((SymbolicTupleType) gbarrierType
				.getDynamicType(universe), Arrays.asList(nprocs, procMapArray,
				inBarrierArray, numInBarrier));
		state = primaryExecutor.malloc(source, state, pid, process, lhs,
				scopeExpression, scope, gbarrierType, gbarrierObj);
		return state;
	}

}
