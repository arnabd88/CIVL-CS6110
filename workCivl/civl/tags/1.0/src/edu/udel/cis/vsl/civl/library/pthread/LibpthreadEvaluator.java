package edu.udel.cis.vsl.civl.library.pthread;

import java.util.List;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryEvaluator;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;

public class LibpthreadEvaluator extends BaseLibraryEvaluator implements
		LibraryEvaluator {

	private IntObject fourObject;

	public LibpthreadEvaluator(String name, Evaluator evaluator,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer, CIVLConfiguration civlConfig,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, evaluator, modelFactory, symbolicUtil, symbolicAnalyzer,
				civlConfig, libEvaluatorLoader);
		this.fourObject = universe.intObject(4);
	}

	@Override
	public Evaluation evaluateGuard(CIVLSource source, State state, int pid,
			String function, List<Expression> arguments)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression[] argumentValues;
		int numArgs;
		BooleanExpression guard;
		int processIdentifier = state.getProcessState(pid).identifier();
		String process = "p" + processIdentifier + " (id = " + pid + ")";

		numArgs = arguments.size();
		argumentValues = new SymbolicExpression[numArgs];
		for (int i = 0; i < numArgs; i++) {
			Evaluation eval = null;

			try {
				eval = evaluator.evaluate(state, pid, arguments.get(i));
			} catch (UnsatisfiablePathConditionException e) {
				// the error that caused the unsatisfiable path condition should
				// already have been reported.
				return new Evaluation(state, universe.falseExpression());
			}
			argumentValues[i] = eval.value;
			state = eval.state;
		}
		switch (function) {
		case "pthread_mutex_lock":
			return guard_of_mutex_lock(state, processIdentifier, process,
					arguments, argumentValues);
		default:
			guard = universe.trueExpression();
		}
		return new Evaluation(state, guard);
	}

	/**
	 * 
	 * typedef struct { int count; $proc owner; int lock; int prioceiling;
	 * pthread_mutexattr_t *attr; } pthread_mutex_t;
	 * 
	 * @param state
	 * @param pid
	 * @param arguments
	 * @param argumentValues
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation guard_of_mutex_lock(State state, int pid,
			String process, List<Expression> arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		Evaluation eval;
		CIVLSource mutexSource = arguments.get(0).getSource();
		SymbolicExpression mutex_pointer = argumentValues[0];
		SymbolicExpression mutex;
		SymbolicExpression mutex_attr_pointer;
		SymbolicExpression mutex_attr;
		NumericExpression mutex_type;
		NumericExpression mutex_lock;
		NumericExpression mutex_robust;
		SymbolicExpression mutex_owner;
		int owner_id;// if(owner_id == pid)

		eval = evaluator.dereference(mutexSource, state, process,
				mutex_pointer, false);
		state = eval.state;
		mutex = eval.value;
		mutex_lock = (NumericExpression) universe.tupleRead(mutex, twoObject);
		mutex_owner = universe.tupleRead(mutex, oneObject);
		owner_id = modelFactory.getProcessId(mutexSource, mutex_owner);

		mutex_attr_pointer = universe.tupleRead(mutex, fourObject);
		eval = evaluator.dereference(mutexSource, state, process,
				mutex_attr_pointer, false);
		state = eval.state;
		mutex_attr = eval.value;
		mutex_type = (NumericExpression) universe.tupleRead(mutex_attr,
				threeObject);
		mutex_robust = (NumericExpression) universe.tupleRead(mutex_attr,
				zeroObject);
		if (mutex_type.isZero() || mutex_type == two)// PTHREAD_MUTEX_NORMAL
		{// TODO
			if (!mutex_lock.isZero()) {
				if (modelFactory.isProcNull(mutexSource, mutex_owner))// TODO
																		// proc_null
																		// checking
				{
					if (!mutex_robust.isOne()) {
						return new Evaluation(state, this.trueValue);
					}
				} else {
					if (owner_id == pid) {
						return new Evaluation(state, this.trueValue);
					}
				}
			} else {
				return new Evaluation(state, this.trueValue);
			}
		} else {
			return new Evaluation(state, this.trueValue);
		}
		return new Evaluation(state, this.falseValue);
	}

}
