package edu.udel.cis.vsl.civl.library.concurrency;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryExecutor;
import edu.udel.cis.vsl.civl.log.IF.CIVLExecutionException;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.Certainty;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.ModelConfiguration;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SARLException;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.expr.Expressions;

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
			SymbolicAnalyzer symbolicAnalyzer, CIVLConfiguration civlConfig,
			LibraryExecutorLoader libExecutorLoader,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, primaryExecutor, modelFactory, symbolicUtil,
				symbolicAnalyzer, civlConfig, libExecutorLoader,
				libEvaluatorLoader);
	}

	/* ******************** Methods from LibraryExecutor ******************* */

	@Override
	public State execute(State state, int pid, CallOrSpawnStatement statement,
			String functionName) throws UnsatisfiablePathConditionException {
		return executeWork(state, pid, statement, functionName);
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
	private State executeWork(State state, int pid, CallOrSpawnStatement call,
			String functionName) throws UnsatisfiablePathConditionException {
		Expression[] arguments;
		SymbolicExpression[] argumentValues;
		LHSExpression lhs;
		int numArgs;
		String process = state.getProcessState(pid).name() + "(id=" + pid + ")";

		numArgs = call.arguments().size();
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
		switch (functionName) {
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
		case "$gcollect_checker_create":
			state = executeGcollectCheckerCreate(state, pid, process, lhs,
					arguments, argumentValues, call.getSource());
			break;
		case "$gcollect_checker_destroy":
			state = executeGcollectCheckerDestroy(state, pid, process,
					arguments, argumentValues, call.getSource());
			break;
		case "$collect_checker_create":
			state = executeCollectCheckerCreate(state, pid, process, lhs,
					arguments, argumentValues, call.getSource());
			break;
		case "$collect_checker_destroy":
			state = this.executeFree(state, pid, process, arguments,
					argumentValues, call.getSource());
			break;
		case "$collect_check":
			state = executeCollectCheck(state, pid, process, lhs, arguments,
					argumentValues, call.getSource());
			break;
		default:
			throw new CIVLUnimplementedFeatureException("the function " + name
					+ " of library concurrency.cvh", call.getSource());
		}
		state = stateFactory.setLocation(state, pid, call.target(),
				call.lhs() != null);
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
		CIVLType barrierType = typeFactory
				.systemType(ModelConfiguration.BARRIER_TYPE);
		Evaluation eval;
		int place_num = ((IntegerNumber) universe
				.extractNumber((NumericExpression) place)).intValue();
		NumericExpression totalPlaces;
		BooleanExpression claim;
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		ResultType resultType;

		if (place_num < 0) {
			throw new CIVLExecutionException(ErrorKind.OTHER,
					Certainty.CONCRETE, process, "Invalid place " + place_num
							+ " used in $barrier_create().", source);
		}
		eval = this.evaluator.dereference(civlsource, state, process, gbarrier,
				false);
		state = eval.state;
		gbarrierObj = eval.value;
		totalPlaces = (NumericExpression) universe.tupleRead(gbarrierObj,
				zeroObject);
		claim = universe.lessThanEquals(universe.integer(place_num),
				totalPlaces);
		resultType = reasoner.valid(claim).getResultType();
		if (!resultType.equals(ResultType.YES)) {
			CIVLExecutionException err = new CIVLExecutionException(
					ErrorKind.OTHER,
					Certainty.CONCRETE,
					process,
					"Place "
							+ place_num
							+ " used in $barrier_create() exceeds the size of the $gbarrier.",
					source);

			this.errorLogger.reportError(err);
			state = this.errorLogger
					.logError(
							source,
							state,
							process,
							symbolicAnalyzer.stateInformation(state),
							claim,
							resultType,
							ErrorKind.OTHER,
							"Place "
									+ place_num
									+ " used in $barrier_create() exceeds the size of the $gbarrier.");
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
		CIVLType gbarrierType = typeFactory
				.systemType(ModelConfiguration.GBARRIER_TYPE);
		BooleanExpression context = state.getPathCondition();

		inBarrierArray = symbolicUtil.newArray(context, universe.booleanType(),
				nprocs, this.falseValue);
		procMapArray = symbolicUtil.newArray(context,
				typeFactory.processSymbolicType(), nprocs,
				modelFactory.nullProcessValue());
		gbarrierObj = universe.tuple((SymbolicTupleType) gbarrierType
				.getDynamicType(universe), Arrays.asList(nprocs, procMapArray,
				inBarrierArray, numInBarrier));
		state = primaryExecutor.malloc(source, state, pid, process, lhs,
				scopeExpression, scope, gbarrierType, gbarrierObj);
		return state;
	}

	// TODO: Make the collective operation checking mechanism more general
	// instead just for MPI programs and stop reporting only MPI_ERRORs
	/**
	 * Executes the system function
	 * <code>$gcollect_checker $gcollect_checker_create($scope scope);</code>,
	 * it creates a <code>$gcollect_checker</code> object and returns a handle
	 * to that object.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The {@link String} identifier of the process
	 * @param lhs
	 *            The Left-hand side expression
	 * @param arguments
	 *            {@link Expressions} of arguments of the function call
	 * @param argumentValues
	 *            {@link SymbolicExpressions} of arguments of the function call
	 * @param source
	 *            {@link CIVLSource} of the function call statement
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeGcollectCheckerCreate(State state, int pid,
			String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression scope = argumentValues[0];
		// incomplete $collect_record array
		SymbolicExpression imcompRecordsArray;
		SymbolicExpression gcollectChecker;
		CIVLType gcollectCheckerType;
		CIVLType collectRecordType;

		gcollectCheckerType = this.typeFactory
				.systemType(ModelConfiguration.GCOLLECT_CHECKER_TYPE);
		collectRecordType = this.typeFactory
				.systemType(ModelConfiguration.COLLECT_RECORD_TYPE);
		imcompRecordsArray = universe.emptyArray(collectRecordType
				.getDynamicType(universe));
		// make initial values of fields of gcollect_checker ready
		gcollectChecker = universe.tuple(
				(SymbolicTupleType) gcollectCheckerType
						.getDynamicType(universe), Arrays.asList(zero,
						imcompRecordsArray));
		state = this.primaryExecutor.malloc(source, state, pid, process, lhs,
				arguments[0], scope, gcollectCheckerType, gcollectChecker);
		return state;
	}

	/**
	 * Creates a local handle of a collective operations checker.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String Identifier of the process
	 * @param lhs
	 *            The left-hand side expression of the statement
	 * @param arguments
	 *            The list of {@link Expressions} of the arguments
	 * @param argumentValues
	 *            The list of {@link SymbolicExpression} of the arguments
	 * @param source
	 *            The CIVL source of the statement
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeCollectCheckerCreate(State state, int pid,
			String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression scope = argumentValues[0];
		SymbolicExpression gchecker = argumentValues[1];
		SymbolicExpression checker;
		CIVLType collectCheckerType;

		collectCheckerType = typeFactory
				.systemType(ModelConfiguration.COLLECT_CHECKER_TYPE);
		checker = universe
				.tuple((SymbolicTupleType) collectCheckerType
						.getDynamicType(universe), Arrays.asList(gchecker));
		state = primaryExecutor.malloc(source, state, pid, process, lhs,
				arguments[0], scope, collectCheckerType, checker);
		return state;
	}

	/**
	 * Destroy a global collective checker
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String Identifier of the process
	 * @param lhs
	 *            The left-hand side expression of the statement
	 * @param arguments
	 *            The list of {@link Expressions} of the arguments
	 * @param argumentValues
	 *            The list of {@link SymbolicExpression} of the arguments
	 * @param source
	 *            The CIVL source of the statement
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeGcollectCheckerDestroy(State state, int pid,
			String process, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression gcheckerHandle = argumentValues[0];
		SymbolicExpression gchecker;
		NumericExpression records_length;
		BooleanExpression claim;
		ResultType resultType;
		Reasoner reasoner;
		Evaluation eval;

		eval = evaluator.dereference(arguments[0].getSource(), state, process,
				gcheckerHandle, false);
		state = eval.state;
		gchecker = eval.value;
		records_length = (NumericExpression) universe.tupleRead(gchecker,
				zeroObject);
		reasoner = universe.reasoner(state.getPathCondition());
		claim = universe.equals(records_length, zero);
		resultType = reasoner.valid(claim).getResultType();
		if (!resultType.equals(ResultType.YES)) {
			state = errorLogger
					.logError(
							source,
							state,
							process,
							symbolicAnalyzer.stateInformation(state),
							claim,
							resultType,
							ErrorKind.MPI_ERROR,
							"There are records remaining in the collective operation checker which means collective "
									+ "operations are not executed right for all processes.\n");
		}
		state = this.executeFree(state, pid, process, arguments,
				argumentValues, source);
		return state;
	}

	/**
	 * Execute the collective checking function:
	 * <code>void $collect_check($collect_checker checker, int place, int nprocs,                                                    
	 *               int routine_tag, int root, int op, int numTypes, void * datatypes)</code>
	 * The execution logic is: The first process for a record will create the
	 * record, and enqueue the record. <br>
	 * Rest processes marks themselves in the corresponding record. <br>
	 * The last marked process dequeue the record. <br>
	 * Since all records for processes must be checked in the same order, the
	 * logic makes sense.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String Identifier of the process
	 * @param lhs
	 *            The left-hand side expression of the statement
	 * @param arguments
	 *            The list of {@link Expressions} of the arguments
	 * @param argumentValues
	 *            The list of {@link SymbolicExpression} of the arguments
	 * @param source
	 *            The CIVL source of the statement
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeCollectCheck(State state, int pid, String process,
			LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression checkhandle = argumentValues[0];
		SymbolicExpression place = argumentValues[1];
		SymbolicExpression nprocs = argumentValues[2];
		SymbolicExpression routine_tag = argumentValues[3];
		SymbolicExpression root = argumentValues[4];
		SymbolicExpression op = argumentValues[5];
		SymbolicExpression numTypes = argumentValues[6];
		SymbolicExpression typesPtr = argumentValues[7];
		SymbolicExpression types;
		SymbolicExpression check, gcheckHandle, gcheck;
		SymbolicExpression records, tail_record;
		SymbolicExpression marksArray; // marks array of a record
		SymbolicExpression modifiedRecord = null;
		BooleanExpression markedElement; // element of a marks array
		BooleanExpression claim;
		NumericExpression records_length;
		NumericExpression numMarked; // number of marked processes in one record
		Number temp;
		IntegerNumber int_numTypes;
		Reasoner reasoner;
		Evaluation eval;
		ResultType resultType;
		// fields indices
		IntObject marksArrayIdx = universe.intObject(5);
		IntObject numMarksIdx = universe.intObject(6);

		// Decides "numTypes", it must be a concrete number.
		reasoner = universe.reasoner(state.getPathCondition());
		temp = reasoner.extractNumber((NumericExpression) numTypes);
		if (temp == null)
			throw new CIVLInternalException(
					"Collective operation checker must know the number of datatypes of a record.\n",
					source);
		int_numTypes = (IntegerNumber) temp;
		assert int_numTypes.intValue() >= 0 && int_numTypes.intValue() < 3 : "CIVL currently only support 1 or 2 "
				+ "datatypes in one collective record. (e.g. MPI_Alltoallw() is not supported)\n";
		if (int_numTypes.intValue() > 0) {
			eval = evaluator.dereference(source, state, process, typesPtr,
					false);
			state = eval.state;
			types = eval.value;
		} else
			types = universe.emptyArray(universe.integerType());
		eval = evaluator
				.dereference(source, state, process, checkhandle, false);
		state = eval.state;
		check = eval.value;
		gcheckHandle = universe.tupleRead(check, zeroObject);
		eval = evaluator.dereference(source, state, process, gcheckHandle,
				false);
		state = eval.state;
		gcheck = eval.value;
		// ------Step 1: Check if the process is the first process for a new
		// record
		records_length = (NumericExpression) universe.tupleRead(gcheck,
				zeroObject);
		claim = universe.equals(records_length, zero);
		resultType = reasoner.valid(claim).getResultType();
		records = universe.tupleRead(gcheck, oneObject);
		if (!resultType.equals(ResultType.YES)) {
			tail_record = universe.arrayRead(records,
					universe.subtract(records_length, one));
			marksArray = universe.tupleRead(tail_record, marksArrayIdx);
			markedElement = (BooleanExpression) universe.arrayRead(marksArray,
					(NumericExpression) place);
			resultType = reasoner.valid(markedElement).getResultType();
		}
		// ------Step 2.1: If the process is the first one for a record, create
		// a new record and enqueue it.
		// ------Step 2.2: If the process is not the first one for a record,
		// check if the record is matched with the existed one in queue and mark
		// itself.
		if (resultType.equals(ResultType.YES)) {
			SymbolicExpression newRecord = this.createANewRecord(state, place,
					nprocs, routine_tag, root, op, numTypes, types);

			records = universe.append(records, newRecord);
			records_length = universe.add(records_length, one);
			modifiedRecord = newRecord;
		} else {// TODO what if there are more than one records in the record
				// queue?
			SymbolicExpression unmarked_record = null;
			NumericExpression loopIdf = zero; // symbolic loop identifier
			boolean isMarked = true;
			boolean isMatched;
			String unmatchMessage;
			List<Object> checkingResults; // return type of the helper function

			while (isMarked) {
				try {
					unmarked_record = universe.arrayRead(records, loopIdf);
					marksArray = universe.tupleRead(unmarked_record,
							marksArrayIdx);
					markedElement = (BooleanExpression) universe.arrayRead(
							marksArray, (NumericExpression) place);
					if (reasoner.valid(markedElement).getResultType()
							.equals(ResultType.NO))
						isMarked = false;
					else
						loopIdf = universe.add(loopIdf, one);
				} catch (SARLException e) {
					throw new CIVLInternalException(
							"Unexpected Collective operation checking exception.\n",
							source);
				}
			}
			assert unmarked_record != null : "Unexpected Collective operation checking exception.\n";
			checkingResults = this.isRecordMatch(state, unmarked_record,
					routine_tag, root, op, numTypes, types);
			isMatched = (boolean) checkingResults.get(0);
			unmatchMessage = (String) checkingResults.get(1);
			resultType = (ResultType) checkingResults.get(2);
			claim = (BooleanExpression) checkingResults.get(3);
			if (!isMatched) {
				assert unmatchMessage != null;
				// checking un-passed
				state = errorLogger.logError(source, state, process,
						symbolicAnalyzer.stateInformation(state), claim,
						resultType, ErrorKind.MPI_ERROR,
						"Collective operation mismatched on field: "
								+ unmatchMessage + ".\n");
			} else {
				SymbolicExpression marked_record;
				// checking passed, mark process itself

				marksArray = universe.tupleRead(unmarked_record, marksArrayIdx);
				marksArray = universe.arrayWrite(marksArray,
						(NumericExpression) place, trueValue);
				numMarked = (NumericExpression) universe.tupleRead(
						unmarked_record, numMarksIdx);
				numMarked = universe.add(numMarked, one);
				marked_record = universe.tupleWrite(unmarked_record,
						marksArrayIdx, marksArray);
				marked_record = universe.tupleWrite(marked_record, numMarksIdx,
						numMarked);
				records = universe.arrayWrite(records, loopIdf, marked_record);
				modifiedRecord = marked_record;
			}
		}
		// ------Step 3: check if the process is the last one marks the record,
		// if it is, dequeue the record.
		assert modifiedRecord != null : "Internal error in collective operation checking";
		numMarked = (NumericExpression) universe.tupleRead(modifiedRecord,
				numMarksIdx);
		claim = universe.equals(numMarked, nprocs);
		resultType = reasoner.valid(claim).getResultType();
		assert !resultType.equals(ResultType.MAYBE) : "Number of marked processes in record should be concrete.";
		if (resultType.equals(ResultType.YES)) {
			records = universe.removeElementAt(records, 0);
			records_length = universe.subtract(records_length, one);
		}
		gcheck = universe.tupleWrite(gcheck, this.zeroObject, records_length);
		gcheck = universe.tupleWrite(gcheck, oneObject, records);
		state = primaryExecutor.assign(source, state, process, gcheckHandle,
				gcheck);
		return state;
	}

	/**
	 * Creates a new record of collective checking mechanism
	 * 
	 * @param state
	 *            The current state
	 * @param place
	 *            The place of the process in the collective checking system
	 * @param nprocs
	 *            The number of processes in the collective checking system
	 * @param routine_tag
	 *            An item of the record
	 * @param root
	 *            An item of the record
	 * @param op
	 *            An item of the record
	 * @param numTypes
	 *            An item of the record
	 * @param datatypesArray
	 *            An item of the record
	 * @return A new record of a collective operation checking system.
	 */
	private SymbolicExpression createANewRecord(State state,
			SymbolicExpression place, SymbolicExpression nprocs,
			SymbolicExpression routine_tag, SymbolicExpression root,
			SymbolicExpression op, SymbolicExpression numTypes,
			SymbolicExpression datatypesArray) {
		SymbolicExpression newRecord;
		SymbolicExpression newMarks;
		List<SymbolicExpression> newRecordComponents = new LinkedList<>();
		CIVLType collectRecordType = typeFactory
				.systemType(ModelConfiguration.COLLECT_RECORD_TYPE);

		newMarks = symbolicUtil.newArray(state.getPathCondition(),
				universe.booleanType(), (NumericExpression) nprocs,
				this.falseValue);
		newMarks = universe.arrayWrite(newMarks, (NumericExpression) place,
				this.trueValue);
		newRecordComponents.add(routine_tag);
		newRecordComponents.add(root);
		newRecordComponents.add(op);
		newRecordComponents.add(numTypes);
		newRecordComponents.add(datatypesArray);
		newRecordComponents.add(newMarks);
		newRecordComponents.add(one);
		newRecord = universe.tuple(
				(SymbolicTupleType) collectRecordType.getDynamicType(universe),
				newRecordComponents);
		return newRecord;
	}

	/**
	 * Check if a record is matched with a given group of values of another
	 * record. Returns a {@link List} of four objects: {@link Boolean} result,
	 * {@link String} error information, {@link ResultType} resultType,
	 * {@link BooleanExpression} claim
	 * 
	 * @param state
	 *            The current state
	 * @param unmarked_record
	 *            The record in queue which is used to compare
	 * @param routine_tag
	 *            A item of a record
	 * @param root
	 *            A item of a record
	 * @param op
	 *            A item of a record
	 * @param numTypes
	 *            A item of a record
	 * @param datatypesArray
	 *            A item of a record
	 * @return a {@link List} of four objects: {@link Boolean} result,
	 *         {@link String} error information, {@link ResultType} resultType,
	 *         {@link BooleanExpression} claim
	 */
	private List<Object> isRecordMatch(State state,
			SymbolicExpression unmarked_record, SymbolicExpression routine_tag,
			SymbolicExpression root, SymbolicExpression op,
			SymbolicExpression numTypes, SymbolicExpression datatypesArray) {
		ResultType resultType;
		BooleanExpression claim;
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		IntObject routineTagIdx = this.zeroObject;
		IntObject rootIdx = oneObject;
		IntObject opIdx = twoObject;
		IntObject numTypesIdx = universe.intObject(3);
		IntObject typesIdx = universe.intObject(4);

		claim = universe
				.equals(universe.tupleRead(unmarked_record, routineTagIdx),
						routine_tag);
		resultType = reasoner.valid(claim).getResultType();
		if (!resultType.equals(ResultType.YES))
			return Arrays.asList(false, "routine_tag", resultType, claim);
		claim = universe.equals(universe.tupleRead(unmarked_record, rootIdx),
				root);
		resultType = reasoner.valid(claim).getResultType();
		if (!resultType.equals(ResultType.YES))
			return Arrays.asList(false, "root", resultType, claim);
		claim = universe.equals(universe.tupleRead(unmarked_record, opIdx), op);
		resultType = reasoner.valid(claim).getResultType();
		if (!resultType.equals(ResultType.YES))
			return Arrays.asList(false, "operation", resultType, claim);
		claim = universe.equals(
				universe.tupleRead(unmarked_record, numTypesIdx), numTypes);
		claim = universe.and(claim, universe.equals(
				universe.tupleRead(unmarked_record, typesIdx), datatypesArray));
		resultType = reasoner.valid(claim).getResultType();
		if (!resultType.equals(ResultType.YES))
			return Arrays.asList(false, "datatypes", resultType, claim);
		return Arrays.asList(Boolean.TRUE, (Object) null, (Object) null,
				(Object) null);
	}
}
