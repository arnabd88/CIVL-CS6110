package edu.udel.cis.vsl.civl.library.pthread;

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
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

public class LibpthreadEvaluator extends BaseLibraryEvaluator implements
		LibraryEvaluator {

	public LibpthreadEvaluator(String name, Evaluator evaluator,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer, CIVLConfiguration civlConfig,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, evaluator, modelFactory, symbolicUtil, symbolicAnalyzer,
				civlConfig, libEvaluatorLoader);
	}

	@Override
	public Evaluation evaluateGuard(CIVLSource source, State state, int pid,
			String function, Expression[] arguments)
			throws UnsatisfiablePathConditionException {
		int numArgs = arguments.length;
		SymbolicExpression[] argumentValues = new SymbolicExpression[numArgs];
		Evaluation eval;

		for (int i = 0; i < numArgs; i++) {
			eval = this.evaluator.evaluate(state, pid, arguments[i]);
			state = eval.state;
			argumentValues[i] = eval.value;
		}
		switch (function) {
		case "$pthread_gpool_join":
			return evaluateGuard_pthread_gpool_join(source, state, pid,
					function, arguments, argumentValues);
		default:
			return super.evaluateGuard(source, state, pid, function, arguments);
		}
	}

	private Evaluation evaluateGuard_pthread_gpool_join(CIVLSource source,
			State state, int pid, String function, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression gpool = argumentValues[0];
		Evaluation eval;
		SymbolicExpression gpoolObj, threads;
		String process = state.getProcessState(pid).name();
		int numThreads;

		eval = this.evaluator.dereference(source, state, process, arguments[0],
				gpool, false);
		gpoolObj = eval.value;
		state = eval.state;
		threads = this.universe.tupleRead(gpoolObj, zeroObject);
		numThreads = this.symbolicUtil.extractInt(source,
				universe.length(threads));
		for (int i = 0; i < numThreads; i++) {
			SymbolicExpression threadObj, threadPtr = universe.arrayRead(
					threads, universe.integer(i));
			SymbolicExpression pidValue;
			int pidInt;

			if (this.symbolicAnalyzer.isDerefablePointer(state, threadPtr).right != ResultType.YES)
				continue;
			eval = this.evaluator.dereference(source, state, process, null,
					universe.arrayRead(threads, universe.integer(i)), false);
			threadObj = eval.value;
			state = eval.state;
			pidValue = universe.tupleRead(threadObj, this.zeroObject);
			pidInt = modelFactory.getProcessId(source, pidValue);
			if (!modelFactory.isProcessIdNull(pidInt)
					&& modelFactory.isPocessIdDefined(pidInt))
				if (!state.getProcessState(pidInt).hasEmptyStack())
					return new Evaluation(state, this.falseValue);
		}
		return new Evaluation(state, this.trueValue);
	}
}
