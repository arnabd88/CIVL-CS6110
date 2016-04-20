package edu.udel.cis.vsl.civl.library.pthread;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.IF.BaseLibraryExecutor;
import edu.udel.cis.vsl.civl.log.IF.CIVLExecutionException;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.Certainty;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;

public class LibpthreadExecutor extends BaseLibraryExecutor implements
		LibraryExecutor {

	private IntObject fourObject;

	public LibpthreadExecutor(String name, Executor primaryExecutor,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			CIVLConfiguration civlConfig) {
		super(name, primaryExecutor, modelFactory, symbolicUtil, civlConfig);
		this.fourObject = universe.intObject(4);
	}

	@Override
	public State execute(State state, int pid, CallOrSpawnStatement statement)
			throws UnsatisfiablePathConditionException {
		return executeWork(state, pid, statement);
	}

	private State executeWork(State state, int pid,
			CallOrSpawnStatement statement)
			throws UnsatisfiablePathConditionException {
		Identifier name;
		Expression[] arguments;
		SymbolicExpression[] argumentValues;
		int numArgs;
		CIVLSource source = statement.getSource();
		LHSExpression lhs = statement.lhs();
		int processIdentifier = state.getProcessState(pid).identifier();
		String process = "p" + processIdentifier + " (id = " + pid + ")";

		numArgs = statement.arguments().size();
		name = statement.function().name();
		arguments = new Expression[numArgs];
		argumentValues = new SymbolicExpression[numArgs];
		for (int i = 0; i < numArgs; i++) {
			Evaluation eval;

			arguments[i] = statement.arguments().get(i);
			eval = evaluator.evaluate(state, pid, arguments[i]);
			argumentValues[i] = eval.value;
			state = eval.state;
		}
		switch (name.name()) {
		case "pthread_mutex_lock":
			state = execute_pthread_mutex_lock(state, pid, process, lhs,
					arguments, argumentValues, source);
			break;
		case "pthread_mutex_unlock":
			state = execute_pthread_mutex_unlock(state, pid, process, lhs,
					arguments, argumentValues, source);
			break;
		case "_add_thread":
			state = execute_add_thread(state, pid, process, arguments,
					argumentValues, source);
			break;
		default:
		}
		state = stateFactory.setLocation(state, pid, statement.target());
		return state;
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

	/**
	 * * typedef struct { int count; $proc owner; int lock; int prioceiling;
	 * pthread_mutexattr_t *attr; } pthread_mutex_t;
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
	private State execute_pthread_mutex_lock(State state, int pid,
			String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		Evaluation eval;
		CIVLSource mutexSource = arguments[0].getSource();
		SymbolicExpression mutex_pointer = argumentValues[0];
		SymbolicExpression mutex;
		SymbolicExpression mutex_attr;
		SymbolicExpression mutex_attr_pointer;
		SymbolicExpression mutex_owner;
		NumericExpression mutex_lock;
		NumericExpression mutex_type;
		NumericExpression mutex_robust;
		NumericExpression mutex_count;
		NumericExpression tmp;
		int owner_id;
		SymbolicExpression pidValue = modelFactory.processValue(pid);

		// TODO: check the case for "return EOWNERDEAD".
		eval = evaluator.dereference(mutexSource, state, process,
				mutex_pointer, false);
		state = eval.state;
		mutex = eval.value;
		mutex_count = (NumericExpression) universe.tupleRead(mutex, zeroObject);
		mutex_lock = (NumericExpression) universe.tupleRead(mutex, twoObject);
		mutex_owner = universe.tupleRead(mutex, oneObject);
		owner_id = modelFactory.getProcessId(mutexSource, mutex_owner);
		mutex_attr_pointer = universe.tupleRead(mutex, fourObject);
		mutexSource = arguments[0].getSource();
		eval = evaluator.dereference(mutexSource, state, process,
				mutex_attr_pointer, false);
		state = eval.state;
		mutex_attr = eval.value;
		mutex_robust = (NumericExpression) universe
				.tupleRead(mutex, zeroObject);
		mutex_type = (NumericExpression) universe.tupleRead(mutex_attr,
				threeObject);

		if (mutex_type.isZero() || mutex_type == two) {
			if (!mutex_lock.isZero()) {
				if (modelFactory.isProcNull(mutexSource, mutex_owner)) {
					if (!mutex_robust.isOne()) {
						state = primaryExecutor.assign(state, pid, process,
								lhs, two);
						throw new CIVLExecutionException(
								ErrorKind.DEADLOCK,
								Certainty.CONCRETE,
								process,
								"Mutex lock owner"
										+ " has terminated without releasing mutex",
								source);
					}
				} else {
					if (owner_id == pid) {
						throw new CIVLExecutionException(ErrorKind.OTHER,
								Certainty.CONCRETE, process,
								"Relock attempted on mutex", source);
					}
				}
			}
			mutex = universe.tupleWrite(mutex, twoObject, one);
			mutex = universe.tupleWrite(mutex, oneObject, pidValue);
		} else {
			tmp = mutex_lock;
			mutex = universe.tupleWrite(mutex, twoObject, one);
			if (tmp.isZero()) {
				mutex = universe.tupleWrite(mutex, oneObject, pidValue);
				mutex = universe.tupleWrite(mutex, zeroObject, one);
			} else {
				if (owner_id == pid) {
					universe.add(mutex_count, one);
					mutex = universe.tupleWrite(mutex, oneObject, pidValue);
					mutex = universe.tupleWrite(mutex, zeroObject, mutex_count);
				} else {
					throw new CIVLExecutionException(
							ErrorKind.OTHER,
							Certainty.CONCRETE,
							process,
							"Current thread does not already own recursive mutex",
							source);
				}
			}

		}

		state = primaryExecutor.assign(mutexSource, state, process,
				mutex_pointer, mutex);
		if (lhs != null) {

			state = primaryExecutor.assign(state, pid, process, lhs, zero);
		}
		return state;
	}
	
	/**
	 * * typedef struct { int count; $proc owner; int lock; int prioceiling;
	 * pthread_mutexattr_t *attr; } pthread_mutex_t;
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
	private State execute_pthread_mutex_unlock(State state, int pid,
			String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		Evaluation eval;
		CIVLSource mutexSource = arguments[0].getSource();
		SymbolicExpression mutex_pointer = argumentValues[0];
		SymbolicExpression mutex;
		SymbolicExpression mutex_attr;
		SymbolicExpression mutex_attr_pointer;
		SymbolicExpression mutex_owner;
		NumericExpression mutex_lock;
		NumericExpression mutex_type;
		NumericExpression mutex_count;
		int owner_id;
		
		eval = evaluator.dereference(mutexSource, state, process,
				mutex_pointer, false);
		state = eval.state;
		mutex = eval.value;
		mutex_count = (NumericExpression) universe.tupleRead(mutex, zeroObject);
		mutex_lock = (NumericExpression) universe.tupleRead(mutex, twoObject);
		mutex_owner = universe.tupleRead(mutex, oneObject);
		owner_id = modelFactory.getProcessId(mutexSource, mutex_owner);
		mutex_attr_pointer = universe.tupleRead(mutex, fourObject);
		mutexSource = arguments[0].getSource();
		eval = evaluator.dereference(mutexSource, state, process, mutex_attr_pointer, false);
		state = eval.state;
		mutex_attr = eval.value;
		mutex_type = (NumericExpression) universe.tupleRead(mutex_attr, threeObject);
		if(mutex_type.isZero()|| mutex_type == two){
			if(mutex_lock.isZero()){
				throw new CIVLExecutionException(ErrorKind.OTHER,
						Certainty.CONCRETE, process, "Attempted to unlock already unlocked lock", source);
			}
			else{
				mutex = universe.tupleWrite(mutex, twoObject, zero);
				//TODO add proc_null assignment to owner
			}
		}
		else{
			if(owner_id==pid){
				universe.subtract(mutex_count, one);
				mutex = universe.tupleWrite(mutex, zeroObject, mutex_count);
				if(mutex_count.isZero()){
					mutex = universe.tupleWrite(mutex, twoObject, one);
					//TODO add proc_null assignment to owner
				}
			}
			else{
				throw new CIVLExecutionException(ErrorKind.OTHER,
						Certainty.CONCRETE, process, "Recursive mutex attempts unlock without being owner", source);
			}
			
		}
		state = primaryExecutor.assign(mutexSource, state, process,
				mutex_pointer, mutex);
		if (lhs != null) {
			
			state = primaryExecutor.assign(state, pid, process, lhs, zero);
		}
		return state;
	}
}
