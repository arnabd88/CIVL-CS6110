package edu.udel.cis.vsl.civl.library.pthread;

import java.util.Arrays;
import java.util.LinkedList;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryExecutor;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.ModelConfiguration;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLStructOrUnionType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class LibpthreadExecutor extends BaseLibraryExecutor implements
		LibraryExecutor {

	private CIVLType gpoolType;
	private SymbolicTupleType gpoolSymbolicType;
	private CIVLType poolType;
	private SymbolicTupleType poolSymbolicType;
	private CIVLArrayType pthreadArrayType;
	@SuppressWarnings("unused")
	private SymbolicArrayType pthreadArraySymbolicType;
	private CIVLType pthreadPointerType;
	private SymbolicType pthreadPointerSymbolicType;

	public LibpthreadExecutor(String name, Executor primaryExecutor,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer, CIVLConfiguration civlConfig,
			LibraryExecutorLoader libExecutorLoader,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, primaryExecutor, modelFactory, symbolicUtil,
				symbolicAnalyzer, civlConfig, libExecutorLoader,
				libEvaluatorLoader);
		this.gpoolType = this.typeFactory
				.systemType(ModelConfiguration.PTHREAD_GPOOL);
		this.gpoolSymbolicType = (SymbolicTupleType) this.gpoolType
				.getDynamicType(universe);
		this.poolType = this.typeFactory
				.systemType(ModelConfiguration.PTHREAD_POOL);
		this.poolSymbolicType = (SymbolicTupleType) this.poolType
				.getDynamicType(universe);
		pthreadArrayType = (CIVLArrayType) ((CIVLStructOrUnionType) this.gpoolType)
				.getField(0).type();
		pthreadArraySymbolicType = (SymbolicArrayType) pthreadArrayType
				.getDynamicType(universe);
		pthreadPointerType = pthreadArrayType.elementType();
		this.pthreadPointerSymbolicType = pthreadPointerType
				.getDynamicType(universe);
	}

	@Override
	public State execute(State state, int pid, CallOrSpawnStatement statement,
			String functionName) throws UnsatisfiablePathConditionException {
		return executeWork(state, pid, statement, functionName);
	}

	private State executeWork(State state, int pid,
			CallOrSpawnStatement statement, String functionName)
			throws UnsatisfiablePathConditionException {
		Expression[] arguments;
		SymbolicExpression[] argumentValues;
		int numArgs;
		CIVLSource source = statement.getSource();
		int processIdentifier = state.getProcessState(pid).identifier();
		String process = "p" + processIdentifier + " (id = " + pid + ")";
		LHSExpression lhs = statement.lhs();

		numArgs = statement.arguments().size();
		arguments = new Expression[numArgs];
		argumentValues = new SymbolicExpression[numArgs];
		for (int i = 0; i < numArgs; i++) {
			Evaluation eval;

			arguments[i] = statement.arguments().get(i);
			eval = evaluator.evaluate(state, pid, arguments[i]);
			argumentValues[i] = eval.value;
			state = eval.state;
		}
		switch (functionName) {
		case "$pthread_gpool_thread":
			state = execute_pthread_gpool_thread(state, pid, process, lhs,
					arguments, argumentValues, source);
			break;
		case "$pthread_gpool_size":
			state = execute_pthread_gpool_size(state, pid, process, lhs,
					arguments, argumentValues, source);
			break;
		case "$pthread_gpool_create":
			state = execute_pthread_gpool_create(state, pid, process, lhs,
					arguments, argumentValues, source);
			break;
		case "$pthread_pool_create":
			state = execute_pthread_pool_create(state, pid, process, lhs,
					arguments, argumentValues, source);
			break;
		case "$pthread_gpool_add":
			state = execute_pthread_gpool_add(state, pid, process, arguments,
					argumentValues, source);
			break;
		// case "$pthread_pool_exit":
		// state = execute_pthread_pool_exit(state, pid, process, arguments,
		// argumentValues, source);
		// break;
		case "$pthread_pool_get_terminated":
			state = execute_pthread_pool_get_terminated(state, pid, process,
					lhs, arguments, argumentValues, source);
			break;
		case "$pthread_pool_get_id":
			state = this.execute_pthread_pool_get_id(state, pid, process, lhs,
					arguments, argumentValues, source);
			break;
		case "_add_thread":
			state = execute_add_thread(state, pid, process, arguments,
					argumentValues, source);
			break;
		case "$pthread_pool_terminates":
			state = execute_pthread_pool_terminates(state, pid, process,
					arguments, argumentValues, source);
			break;
		case "$pthread_pool_is_terminated":
			state = execute_pthread_pool_is_terminated(state, pid, process,
					lhs, arguments, argumentValues, source);
			break;
		case "$pthread_pool_thread":
			state = execute_pthread_pool_thread(state, pid, process, lhs,
					arguments, argumentValues, source);
			break;
		default:
			throw new CIVLUnimplementedFeatureException(
					"execution of function " + functionName
							+ " in pthread library", source);
		}
		state = stateFactory.setLocation(state, pid, statement.target(),
				statement.lhs() != null);
		return state;
	}

	private State execute_pthread_pool_thread(State state, int pid,
			String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression pool = argumentValues[0], poolObj;
		Evaluation eval;
		SymbolicExpression threadPointer;

		eval = this.evaluator.dereference(source, state, process, pool, false);
		poolObj = eval.value;
		state = eval.state;
		threadPointer = universe.tupleRead(poolObj, this.twoObject);
		eval = this.evaluator.dereference(source, state, process,
				threadPointer, false);
		state = eval.state;
		if (lhs != null)
			state = this.primaryExecutor.assign(state, pid, process, lhs,
					eval.value);
		return state;
	}

	/**
	 * _Bool $pthread_pool_is_terminated($pthread_pool_t pool, $proc pid);
	 * 
	 * @param state
	 * @param pid
	 * @param process
	 * @param lhs
	 * @param arguments
	 * @param argumentValues
	 * @param source
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State execute_pthread_pool_is_terminated(State state, int pid,
			String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		// TODO Auto-generated method stub
		SymbolicExpression pool = argumentValues[0], proc = argumentValues[1];
		SymbolicExpression poolObject, gpool, gpoolObject, threads;
		NumericExpression numThreads;
		int numThreads_int;
		Evaluation eval;
		SymbolicExpression result = trueValue;

		eval = this.evaluator.dereference(source, state, process, pool, false);
		poolObject = eval.value;
		state = eval.state;
		gpool = universe.tupleRead(poolObject, zeroObject);
		eval = this.evaluator.dereference(source, state, process, gpool, false);
		state = eval.state;
		gpoolObject = eval.value;
		threads = universe.tupleRead(gpoolObject, zeroObject);
		numThreads = universe.length(threads);
		numThreads_int = symbolicUtil.extractInt(source, numThreads);
		for (int i = 0; i < numThreads_int; i++) {
			SymbolicExpression threadPointer = universe.arrayRead(threads,
					universe.integer(i));
			SymbolicExpression threadObj, threadId;

			eval = this.evaluator.dereference(source, state, process,
					threadPointer, false);
			threadObj = eval.value;
			state = eval.state;
			threadId = universe.tupleRead(threadObj, zeroObject);
			if (universe.equals(threadId, proc).isTrue()) {
				result = universe.tupleRead(threadObj, twoObject);
				break;
			}
		}
		if (lhs != null)
			state = this.primaryExecutor.assign(state, pid, process, lhs,
					result);
		return state;
	}

	private State execute_pthread_gpool_thread(State state, int pid,
			String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression gpool = argumentValues[0];
		NumericExpression index = (NumericExpression) argumentValues[1];
		SymbolicExpression gpoolObject, threadPointer, threadObj, result;
		Evaluation eval;

		eval = this.evaluator.dereference(source, state, process, gpool, false);
		gpoolObject = eval.value;
		state = eval.state;
		threadPointer = universe.arrayRead(
				universe.tupleRead(gpoolObject, zeroObject), index);
		if (!symbolicUtil.isValidPointer(threadPointer))
			result = modelFactory.nullProcessValue();
		else {
			eval = this.evaluator.dereference(source, state, process,
					threadPointer, false);
			threadObj = eval.value;
			state = eval.state;
			result = universe.tupleRead(threadObj, zeroObject);
		}
		if (lhs != null)
			state = this.primaryExecutor.assign(state, pid, process, lhs,
					result);
		return state;
	}

	/**
	 * int $pthread_gpool_size($pthread_gpool_t gpool);
	 * 
	 * @param state
	 * @param pid
	 * @param process
	 * @param lhs
	 * @param arguments
	 * @param argumentValues
	 * @param source
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State execute_pthread_gpool_size(State state, int pid,
			String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression gpool = argumentValues[0];
		SymbolicExpression gpoolObject, result;
		Evaluation eval;

		if (symbolicUtil.isValidPointer(gpool)) {
			eval = this.evaluator.dereference(source, state, process, gpool,
					false);
			gpoolObject = eval.value;
			state = eval.state;
			result = universe.length(universe
					.tupleRead(gpoolObject, zeroObject));
		} else
			result = zero;
		if (lhs != null)
			state = this.primaryExecutor.assign(state, pid, process, lhs,
					result);
		return state;
	}

	/**
	 * void $pthread_pool_terminates($pthread_pool_t pool);
	 * 
	 * 
	 * @param state
	 * @param pid
	 * @param process
	 * @param arguments
	 * @param argumentValues
	 * @param source
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State execute_pthread_pool_terminates(State state, int pid,
			String process, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression pool = argumentValues[0], poolObj;
		Evaluation eval;
		SymbolicExpression threadPointer;
		SymbolicExpression threadTermPointer, threadExitValuePointer;

		eval = this.evaluator.dereference(source, state, process, pool, false);
		poolObj = eval.value;
		state = eval.state;
		threadPointer = universe.tupleRead(poolObj, this.twoObject);
		if (this.symbolicUtil.isValidPointer(threadPointer)) {
			threadTermPointer = this.symbolicUtil.makePointer(threadPointer,
					universe.tupleComponentReference(
							symbolicUtil.getSymRef(threadPointer),
							this.twoObject));
			state = this.primaryExecutor.assign(source, state, process,
					threadTermPointer, trueValue);
			threadExitValuePointer = this.symbolicUtil.makePointer(
					threadPointer, universe.tupleComponentReference(
							symbolicUtil.getSymRef(threadPointer),
							this.threeObject));
			state = this.primaryExecutor.assign(source, state, process,
					threadExitValuePointer, argumentValues[1]);
		}
		return state;
	}

	// * int $pthread_pool_get_oid($pthread_pool pool);
	private State execute_pthread_pool_get_id(State state, int pid,
			String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression threadPointer = universe.tupleRead(
				argumentValues[0], this.twoObject);
		Evaluation eval = this.evaluator.dereference(source, state, process,
				threadPointer, false);
		SymbolicExpression thread = eval.value;

		state = eval.state;
		if (lhs != null)
			state = this.primaryExecutor.assign(state, pid, process, lhs,
					universe.tupleRead(thread, this.twoObject));
		return state;
	}

	// * _Bool $pthread_pool_get_terminated($pthread_pool pool);
	/*
	 * struct pthread_t{ $proc thr; const pthread_attr_t attr; int pid; _Bool
	 * terminated; };
	 */
	private State execute_pthread_pool_get_terminated(State state, int pid,
			String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression threadPointer = universe.tupleRead(
				argumentValues[0], this.twoObject);
		Evaluation eval = this.evaluator.dereference(source, state, process,
				threadPointer, false);
		SymbolicExpression thread = eval.value;

		state = eval.state;
		if (lhs != null)
			state = this.primaryExecutor.assign(state, pid, process, lhs,
					universe.tupleRead(thread, this.threeObject));
		return state;
	}

	// /**
	// * void $pthread_pool_exit($pthread_pool pool);
	// *
	// * @param state
	// * @param pid
	// * @param process
	// * @param arguments
	// * @param argumentValues
	// * @param source
	// * @return
	// * @throws UnsatisfiablePathConditionException
	// */
	// private State execute_pthread_pool_exit(State state, int pid,
	// String process, Expression[] arguments,
	// SymbolicExpression[] argumentValues, CIVLSource source)
	// throws UnsatisfiablePathConditionException {
	// SymbolicExpression pthreadPointer = universe.tupleRead(
	// argumentValues[0], this.twoObject);
	// SymbolicExpression fieldPointer = this.symbolicUtil.makePointer(
	// pthreadPointer, universe.tupleComponentReference(
	// this.symbolicUtil.getSymRef(pthreadPointer),
	// this.threeObject));
	//
	// return this.primaryExecutor.assign(source, state, process,
	// fieldPointer, trueValue);
	// }

	/**
	 * void $pthread_gpool_add($pthread_gpool gpool, pthread_t * thread);
	 * 
	 * @param state
	 * @param pid
	 * @param process
	 * @param arguments
	 * @param argumentValues
	 * @param source
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State execute_pthread_gpool_add(State state, int pid,
			String process, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression gpool = argumentValues[0], threadPointer = argumentValues[1];
		Evaluation eval;
		SymbolicExpression gpoolObj, threads;

		eval = this.evaluator.dereference(source, state, process, gpool, false);
		gpoolObj = eval.value;
		state = eval.state;
		threads = universe.tupleRead(gpoolObj, this.zeroObject);
		threads = universe.append(threads, threadPointer);
		gpoolObj = universe.tupleWrite(gpoolObj, zeroObject, threads);
		return this.primaryExecutor.assign(source, state, process, gpool,
				gpoolObj);
	}

	/**
	 * $pthread_pool $pthread_pool_create ($scope scope, $pthread_gpool gpool);
	 * 
	 * 
	 * struct _pthread_pool_t{ $pthread_gpool gpool; $proc tid; pthread_t *
	 * thread; };
	 * 
	 * @param state
	 * @param pid
	 * @param process
	 * @param lhs
	 * @param arguments
	 * @param argumentValues
	 * @param source
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State execute_pthread_pool_create(State state, int pid,
			String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression scopeValue = argumentValues[0], gpool = argumentValues[1];
		SymbolicExpression tid = modelFactory.processValue(pid);
		SymbolicExpression gpoolObject;
		Evaluation eval;
		SymbolicExpression threadPointer, pool;

		eval = this.evaluator.dereference(source, state, process, gpool, false);
		gpoolObject = eval.value;
		state = eval.state;
		eval = this
				.findThreadFromPool(source, state, process, gpoolObject, pid);
		state = eval.state;
		threadPointer = eval.value;
		pool = universe.tuple(this.poolSymbolicType,
				Arrays.asList(gpool, tid, threadPointer));
		return this.primaryExecutor.malloc(source, state, pid, process, lhs,
				arguments[0], scopeValue, this.poolType, pool);
	}

	/**
	 * 
	 * @param source
	 * @param state
	 * @param process
	 * @param gpool
	 * @param tid
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	Evaluation findThreadFromPool(CIVLSource source, State state,
			String process, SymbolicExpression gpool, int tid)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression threads = universe.tupleRead(gpool, zeroObject);
		NumericExpression nthreads = universe.length(threads);
		int nthreads_int = this.symbolicUtil.extractInt(source, nthreads);
		Evaluation eval;

		for (int i = 0; i < nthreads_int; i++) {
			SymbolicExpression threadPointer = universe.arrayRead(threads,
					universe.integer(i));
			SymbolicExpression thread, threadId;
			int threadId_int;

			eval = this.evaluator.dereference(source, state, process,
					threadPointer, false);
			thread = eval.value;
			state = eval.state;
			threadId = universe.tupleRead(thread, zeroObject);

			threadId_int = modelFactory.getProcessId(source, threadId);
			if (threadId_int == tid)
				return new Evaluation(state, threadPointer);
		}
		return new Evaluation(state, symbolicUtil.nullPointer());
	}

	/**
	 * struct _pthread_gpool_t{ int N; pthread_t threads[]; };
	 * 
	 * @param state
	 * @param pid
	 * @param process
	 * @param arguments
	 * @param argumentValues
	 * @param source
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State execute_pthread_gpool_create(State state, int pid,
			String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression threads = universe.array(
				this.pthreadPointerSymbolicType,
				new LinkedList<SymbolicExpression>());
		SymbolicExpression gpool = universe.tuple(this.gpoolSymbolicType,
				Arrays.asList(threads));
		SymbolicExpression scopeValue = argumentValues[0];

		return this.primaryExecutor.malloc(arguments[0].getSource(), state,
				pid, process, lhs, arguments[0], scopeValue, this.gpoolType,
				gpool);
	}

	private State execute_add_thread(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression poolPointer = argumentValues[0];
		SymbolicExpression threadPointer = argumentValues[1];
		CIVLSource poolPointerSource = arguments[0].getSource();
		SymbolicExpression pool;
		Evaluation eval = evaluator.dereference(poolPointerSource, state,
				process, poolPointer, false);
		NumericExpression len;
		SymbolicExpression threads;

		pool = eval.value;
		state = eval.state;
		len = (NumericExpression) universe.tupleRead(pool, oneObject);
		threads = universe.tupleRead(pool, zeroObject);
		threads = universe.append(threads, threadPointer);
		len = universe.add(len, one);
		pool = universe.tupleWrite(pool, zeroObject, threads);
		pool = universe.tupleWrite(pool, oneObject, len);
		state = primaryExecutor.assign(poolPointerSource, state, process,
				poolPointer, pool);
		return state;
	}

}
