package edu.udel.cis.vsl.civl.library.concurrency;

import java.util.List;

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

public class LibconcurrencyEvaluator extends BaseLibraryEvaluator implements
		LibraryEvaluator {

	public LibconcurrencyEvaluator(String name, Evaluator evaluator,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, evaluator, modelFactory, symbolicUtil, symbolicAnalyzer,
				libEvaluatorLoader);
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
				// the error that caused the unsatifiable path condition should
				// already have been reported.
				return new Evaluation(state, universe.falseExpression());
			}
			argumentValues[i] = eval.value;
			state = eval.state;
		}
		switch (function) {
		case "$barrier_exit":
			try {
				guard = getBarrierExitGuard(state, pid, process, arguments,
						argumentValues);
			} catch (UnsatisfiablePathConditionException e) {
				// the error that caused the unsatifiable path condition should
				// already have been reported.
				return new Evaluation(state, universe.falseExpression());
			}
			break;
		default:
			guard = universe.trueExpression();
		}
		return new Evaluation(state, guard);
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
			String process, List<Expression> arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		CIVLSource source = arguments.get(0).getSource();
		SymbolicExpression barrier = argumentValues[0];
		NumericExpression myPlace;
		SymbolicExpression barrierObj;
		SymbolicExpression gbarrier;
		SymbolicExpression gbarrierObj;
		Evaluation eval = evaluator.dereference(source, state, process,
				barrier, false);
		SymbolicExpression inBarrierArray;
		SymbolicExpression meInBarrier;

		state = eval.state;
		barrierObj = eval.value;
		myPlace = (NumericExpression) universe
				.tupleRead(barrierObj, zeroObject);
		gbarrier = universe.tupleRead(barrierObj, oneObject);
		eval = evaluator.dereference(source, state, process, gbarrier, false);
		state = eval.state;
		gbarrierObj = eval.value;
		inBarrierArray = universe.tupleRead(gbarrierObj, twoObject);
		meInBarrier = universe.arrayRead(inBarrierArray, myPlace);
		if (meInBarrier.isTrue())
			return universe.falseExpression();
		return universe.trueExpression();
	}
}
