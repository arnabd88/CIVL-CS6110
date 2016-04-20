package edu.udel.cis.vsl.civl.library.omp;

import java.util.Arrays;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryExecutor;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.Model;
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
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class LibompExecutor extends BaseLibraryExecutor implements
		LibraryExecutor {
	public LibompExecutor(String name, Executor primaryExecutor,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer, CIVLConfiguration civlConfig,
			LibraryExecutorLoader libExecutorLoader,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, primaryExecutor, modelFactory, symbolicUtil,
				symbolicAnalyzer, civlConfig, libExecutorLoader,
				libEvaluatorLoader);
	}

	@Override
	public State execute(State state, int pid, CallOrSpawnStatement statement)
			throws UnsatisfiablePathConditionException {
		return executeWork(state, pid, statement);
	}

	private State executeWork(State state, int pid, CallOrSpawnStatement call)
			throws UnsatisfiablePathConditionException {
		Expression[] arguments;
		SymbolicExpression[] argumentValues;
		int numArgs = call.arguments().size();
		String functionName = call.function().name().name();
		LHSExpression lhs = call.lhs();
		CIVLSource source = call.getSource();
		int processIdentifier = state.getProcessState(pid).identifier();
		String process = "p" + processIdentifier + " (id = " + pid + ")";

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
		case "$omp_gteam_destroy":
		case "$omp_team_destroy":
		case "$omp_gshared_destroy":
		case "$omp_shared_destroy":
			state = executeFree(state, pid, process, arguments, argumentValues,
					call.getSource());
			break;
		case "$omp_team_create":
			state = execute_team_create(source, state, pid, process, lhs,
					arguments, argumentValues);
			break;
		case "$omp_gshared_create":
			state = execute_gshared_create(source, state, pid, process, lhs,
					arguments, argumentValues);
			break;
		case "$omp_shared_create":
			state = execute_shared_create(source, state, pid, process, lhs,
					arguments, argumentValues);
			break;
		case "$omp_read":
			state = execute_read(source, state, pid, process, arguments,
					argumentValues);
			break;
		case "$omp_write":
			state = execute_write(source, state, pid, process, arguments,
					argumentValues);
			break;
		case "$omp_apply_assoc":
			state = execute_apply_assoc(source, state, pid, process, arguments,
					argumentValues);
			break;
		case "$omp_flush":
			state = execute_flush(source, state, pid, process, arguments,
					argumentValues);
			break;
		case "$omp_flush_all":
			state = execute_flush_all(source, state, pid, process, arguments,
					argumentValues);
			break;
		case "$omp_barrier":
			state = execute_barrier(source, state, pid, process, arguments,
					argumentValues);
			break;
		case "$omp_barrier_and_flush":
			state = execute_barrier_and_flush(source, state, pid, process,
					arguments, argumentValues);
			break;
		case "$omp_arrive_loop":
			state = execute_arrive_loop(source, state, pid, process, lhs,
					arguments, argumentValues);
			break;
		case "$omp_arrive_sections":
			state = execute_arrive_sections(source, state, pid, process, lhs,
					arguments, argumentValues);
			break;
		case "$omp_arrive_single":
			state = execute_arrive_single(source, state, pid, process, lhs,
					arguments, argumentValues);
			break;
		default:
			throw new CIVLUnimplementedFeatureException("The function "
					+ functionName + " is not supported in " + name + ".h.",
					source);

		}
		state = stateFactory.setLocation(state, pid, call.target());
		return state;
	}

	private State execute_arrive_single(CIVLSource source, State state,
			int pid, String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues) {
		// TODO Auto-generated method stub
		return null;
	}

	private State execute_arrive_sections(CIVLSource source, State state,
			int pid, String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues) {
		// TODO Auto-generated method stub
		return null;
	}

	private State execute_arrive_loop(CIVLSource source, State state, int pid,
			String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues) {
		// TODO Auto-generated method stub
		return null;
	}

	/**
	 * Executes $omp_barrier_and_flush(), which Does a barrier on _barrier and a
	 * flush on all shared variables. After this completes, all local copies
	 * will agree with each other and with the shared copy of the variable, and
	 * all state variables will be -1.
	 * 
	 * @param source
	 *            The source code element to be used for error report.
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
	 * @return the new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	private State execute_barrier_and_flush(CIVLSource source, State state,
			int pid, String process, Expression[] arguments,
			SymbolicExpression[] argumentValues) {
		// TODO Auto-generated method stub
		return null;
	}

	private State execute_barrier(CIVLSource source, State state, int pid,
			String process, Expression[] arguments,
			SymbolicExpression[] argumentValues) {
		// TODO Auto-generated method stub
		return null;
	}

	private State execute_flush_all(CIVLSource source, State state, int pid,
			String process, Expression[] arguments,
			SymbolicExpression[] argumentValues) {
		// TODO Auto-generated method stub
		return null;
	}

	private State execute_flush(CIVLSource source, State state, int pid,
			String process, Expression[] arguments,
			SymbolicExpression[] argumentValues) {
		// TODO Auto-generated method stub
		return null;
	}

	private State execute_apply_assoc(CIVLSource source, State state, int pid,
			String process, Expression[] arguments,
			SymbolicExpression[] argumentValues) {
		// TODO Auto-generated method stub
		return null;
	}

	/**
	 * <p>
	 * Called by a thread to write to the shared object pointed to by ref. The
	 * value to be written is taken from the memory unit pointed to by value.
	 * </p>
	 * 
	 * The corresponding system function is:
	 * <code>void $omp_write(void *ref, void *value)</code>.
	 * 
	 * @param source
	 *            the source code information of the call statement for error
	 *            report
	 * @param state
	 *            the pre-state
	 * @param pid
	 *            the PID of the process that triggers this computation
	 * @param process
	 *            the process information for error report
	 * @param arguments
	 *            the static representation of the arguments of the call
	 *            statement
	 * @param argumentValues
	 *            the values of the arguments of the call statement
	 * @return the new state after the system function is invoked
	 * @throws UnsatisfiablePathConditionException
	 */
	private State execute_write(CIVLSource source, State state, int pid,
			String process, Expression[] arguments,
			SymbolicExpression[] argumentValues) {
		// TODO Is this same as copy in pointer.cvh?
		return null;
	}

	/**
	 * <p>
	 * Called by a thread to read a shared object pointed to by ref. The result
	 * of the read is stored in the memory unit pointed to by result.
	 * </p>
	 * 
	 * The corresponding system function is:
	 * <code>void $omp_read(void *result, void *ref)</code>.
	 * 
	 * @param source
	 *            the source code information of the call statement for error
	 *            report
	 * @param state
	 *            the pre-state
	 * @param pid
	 *            the PID of the process that triggers this computation
	 * @param process
	 *            the process information for error report
	 * @param arguments
	 *            the static representation of the arguments of the call
	 *            statement
	 * @param argumentValues
	 *            the values of the arguments of the call statement
	 * @return the new state after the system function is invoked
	 * @throws UnsatisfiablePathConditionException
	 */
	private State execute_read(CIVLSource source, State state, int pid,
			String process, Expression[] arguments,
			SymbolicExpression[] argumentValues) {
		// TODO Is this same as copy in pointer.cvh?
		return null;
	}

	/**
	 * <p>
	 * Creates a local shared object, returning handle to it
	 * </p>
	 * 
	 * The corresponding system function is:
	 * <code>$omp_shared $omp_shared_create($omp_team team, $omp_gshared gshared);</code>
	 * where <code>$omp_shared</code> is a handle type referring to a local view
	 * of the shared object, belonging to a single thread, with reference to the
	 * global object. <code>$omp_shared</code> is defined as the following:
	 * 
	 * <pre>
	 * typedef struct __OMP_shared__ {
	 *   $omp_gshared gshared;
	 *   int tid;
	 * } * $omp_shared;
	 * </pre>
	 * 
	 * @param source
	 *            the source code information of the call statement for error
	 *            report
	 * @param state
	 *            the pre-state
	 * @param pid
	 *            the PID of the process that triggers this computation
	 * @param process
	 *            the process information for error report
	 * @param lhs
	 *            the left-hand-side expression of the call statement
	 * @param arguments
	 *            the static representation of the arguments of the call
	 *            statement
	 * @param argumentValues
	 *            the values of the arguments of the call statement
	 * @return the new state after the system function is invoked
	 * @throws UnsatisfiablePathConditionException
	 */
	private State execute_shared_create(CIVLSource source, State state,
			int pid, String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression team = argumentValues[0], gshared = argumentValues[1];
		CIVLType sharedType = modelFactory.getSystemType(Model.OMP_SHARED_TYPE);
		Evaluation eval;
		SymbolicExpression teamObject, tid, sharedObject;
		SymbolicExpression teamScope = modelFactory.scopeValue(symbolicUtil
				.getDyscopeId(arguments[0].getSource(), team));

		eval = evaluator.dereference(arguments[0].getSource(), state, process,
				team, false);
		state = eval.state;
		teamObject = eval.value;
		tid = universe.tupleRead(teamObject, oneObject);
		sharedObject = universe.tuple(
				(SymbolicTupleType) sharedType.getDynamicType(universe),
				Arrays.asList(gshared, tid));
		// TODO use the scope of the $omp_team handle?
		state = primaryExecutor.malloc(source, state, pid, process, lhs,
				arguments[0], teamScope, sharedType, sharedObject);
		return state;
	}

	/**
	 * <p>
	 * Creates new global shared object, associated to the given global team. A
	 * pointer to the shared variable that this object corresponds to is given.
	 * The new object is initialized by copying the values from the original
	 * variable.
	 * </p>
	 * 
	 * The corresponding system function is:
	 * <code>$omp_gshared $omp_gshared_create($omp_gteam, void *original);</code>
	 * where <code>$omp_gshared</code> is a handle type referring to a global
	 * shared object which is used to represent the state of a shared variable.
	 * <code>$omp_gshared</code> is defined as the following:
	 * 
	 * <pre>
	 * typedef struct __OMP_gshared__ {
	 *   void * original; // pointer to original variable
	 *   int size; // size of original variable
	 *   void * state; // heap allocated state object
	 *   int state_size; // size of state object
	 * } * $omp_gshared;
	 * </pre>
	 * 
	 * @param source
	 *            the source code information of the call statement for error
	 *            report
	 * @param state
	 *            the pre-state
	 * @param pid
	 *            the PID of the process that triggers this computation
	 * @param process
	 *            the process information for error report
	 * @param lhs
	 *            the left-hand-side expression of the call statement
	 * @param arguments
	 *            the static representation of the arguments of the call
	 *            statement
	 * @param argumentValues
	 *            the values of the arguments of the call statement
	 * @return the new state after the system function is invoked
	 * @throws UnsatisfiablePathConditionException
	 */
	private State execute_gshared_create(CIVLSource source, State state,
			int pid, String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression gteam = argumentValues[0], original = argumentValues[1], gteamScope, gsharedObject;
		NumericExpression size = one; // TODO how to compute size?
		NumericExpression stateSize = size;// TODO what's this?
		// the pointer to the state of the original object
		SymbolicExpression statePtr, stateObject;
		CIVLType originalType = symbolicAnalyzer.typeOfObjByPointer(
				arguments[1].getSource(), state, original);
		CIVLType stateType = originalType.copyAs(modelFactory.integerType(),
				universe); // TODO problem: how to infer heap type correctly?
		CIVLType gsharedType = modelFactory
				.getSystemType(Model.OMP_GSHARED_TYPE);
		Evaluation eval = evaluator.initialValueOfStateVariable(source, state,
				pid, stateType);
		Pair<State, SymbolicExpression> mallocResult;

		gteamScope = modelFactory.scopeValue(symbolicUtil.getDyscopeId(
				arguments[0].getSource(), gteam));
		state = eval.state;
		stateObject = eval.value;
		// TODO which scope to be used?
		mallocResult = primaryExecutor.malloc(source, state, pid, process,
				arguments[0], gteamScope, stateType, stateObject);
		statePtr = mallocResult.right;
		state = mallocResult.left;
		gsharedObject = universe.tuple(
				(SymbolicTupleType) gsharedType.getDynamicType(universe),
				Arrays.asList(original, size, statePtr, stateSize));
		state = primaryExecutor.malloc(source, state, pid, process, lhs,
				arguments[0], gteamScope, gsharedType, gsharedObject);
		return state;
	}

	/**
	 * <p>
	 * Executes
	 * <code>$omp_team_create($scope scope, $omp_gteam gteam, int tid)</code>
	 * which creates new local team object for a specific thread.
	 * </p>
	 * 
	 * A global team object is local object belonging to a single thread and
	 * referencing the global team object, and is a handle type.
	 * 
	 * <pre>
	 * typedef struct __OMP_team__ {
	 *   $omp_gteam gteam;
	 *   int tid;
	 * } * $omp_team;
	 * </pre>
	 * 
	 * @param source
	 *            the source code information of the call statement for error
	 *            report
	 * @param state
	 *            the pre-state
	 * @param pid
	 *            the PID of the process that triggers this computation
	 * @param process
	 *            the process information for error report
	 * @param lhs
	 *            the left-hand-side expression of the call statement
	 * @param arguments
	 *            the static representation of the arguments of the call
	 *            statement
	 * @param argumentValues
	 *            the values of the arguments of the call statement
	 * @return the new state after the system function is invoked
	 * @throws UnsatisfiablePathConditionException
	 */
	private State execute_team_create(CIVLSource source, State state, int pid,
			String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		CIVLType teamType = modelFactory.getSystemType(Model.OMP_TEAM_TYPE);
		SymbolicExpression scope = argumentValues[0];
		SymbolicExpression gteamHandle = argumentValues[1];
		SymbolicExpression tid = argumentValues[2];
		SymbolicExpression teamObject = universe.tuple(
				(SymbolicTupleType) teamType.getDynamicType(universe),
				Arrays.asList(gteamHandle, tid));

		state = primaryExecutor.malloc(source, state, pid, process, lhs,
				arguments[0], scope, teamType, teamObject);
		return state;
	}

	/**
	 * <p>
	 * Executes $omp_ws_create($scope scope, $omp_gws, int tid) which creates a
	 * local work-sharing object, which is basically a pair consisting of a
	 * global work-sharing handle and a thread id.
	 * </p>
	 * 
	 * Here is the definition of $omp_ws:
	 * 
	 * <pre>
	 * typedef struct __omp_ws__ {
	 *   int tid;
	 *   $omp_gws gws;
	 * } $omp_ws;
	 * </pre>
	 * 
	 * @param source
	 *            The source code element to be used for error report.
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
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	@SuppressWarnings("unused")
	private State executeWsCreate(CIVLSource source, State state, int pid,
			String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression scope = argumentValues[0];
		Expression scopeExpression = arguments[0];
		SymbolicExpression gws = argumentValues[1];
		SymbolicExpression gwsObj;
		SymbolicExpression wsObj;
		CIVLType wsType = modelFactory.getSystemType(Model.OMP_GTEAM_TYPE);
		SymbolicType dynamicWsType = wsType.getDynamicType(universe);
		SymbolicExpression tid = argumentValues[2];
		SymbolicExpression isInit;
		Evaluation eval;

		eval = this.evaluator.dereference(arguments[1].getSource(), state,
				process, gws, false);
		state = eval.state;
		gwsObj = eval.value;
		isInit = universe.tupleRead(gwsObj, oneObject);
		// TODO report an error if the place has already been taken by other
		// processes.
		assert universe.arrayRead(isInit, (NumericExpression) tid).equals(
				universe.bool(false));
		isInit = universe.arrayWrite(isInit, (NumericExpression) tid,
				universe.bool(true));
		gwsObj = universe.tupleWrite(gwsObj, oneObject, isInit);
		state = this.primaryExecutor.assign(arguments[1].getSource(), state,
				process, gws, gwsObj);
		wsObj = universe.tuple((SymbolicTupleType) dynamicWsType,
				Arrays.asList(tid, gws));
		state = this.primaryExecutor.malloc(source, state, pid, process, lhs,
				scopeExpression, scope, wsType, wsObj);
		return state;
	}
}
