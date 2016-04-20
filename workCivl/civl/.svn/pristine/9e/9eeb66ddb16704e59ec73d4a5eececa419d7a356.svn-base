package edu.udel.cis.vsl.civl.library.civlc;

import java.math.BigInteger;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryEvaluator;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression.BINARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;

public class LibcivlcEvaluator extends BaseLibraryEvaluator implements
		LibraryEvaluator {

	public LibcivlcEvaluator(String name, Evaluator evaluator,
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
		Pair<State, SymbolicExpression[]> argumentsEval;
		BooleanExpression guard;

		switch (function) {
		case "$wait":
			argumentsEval = this.evaluateArguments(state, pid, arguments);
			guard = guardOfWait(state, pid, arguments, argumentsEval.right);
			break;
		case "$waitall":
			argumentsEval = this.evaluateArguments(state, pid, arguments);
			guard = guardOfWaitall(state, pid, arguments, argumentsEval.right);
			break;
		default:
			guard = universe.trueExpression();
		}
		return new Evaluation(state, guard);
	}

	/**
	 * Computes the guard of $wait.
	 * 
	 * @param state
	 * @param pid
	 * @param arguments
	 * @param argumentValues
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private BooleanExpression guardOfWait(State state, int pid,
			Expression[] arguments, SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression joinProcess = argumentValues[0];
		BooleanExpression guard;
		int pidValue;
		Expression joinProcessExpr = arguments[0];

		if (joinProcess.operator() != SymbolicOperator.CONCRETE) {
			String process = state.getProcessState(pid).name() + "(id=" + pid
					+ ")";

			this.errorLogger.logSimpleError(joinProcessExpr.getSource(), state,
					process, symbolicAnalyzer.stateInformation(state),
					ErrorKind.OTHER,
					"the argument of $wait should be concrete, but the actual value is "
							+ joinProcess);
			throw new UnsatisfiablePathConditionException();
		}
		pidValue = modelFactory.getProcessId(joinProcessExpr.getSource(),
				joinProcess);
		if (modelFactory.isPocessIdDefined(pidValue)
				&& !modelFactory.isProcessIdNull(pidValue)
				&& !state.getProcessState(pidValue).hasEmptyStack())
			guard = universe.falseExpression();
		else
			guard = universe.trueExpression();
		return guard;
	}

	/**
	 * void $waitall($proc *procs, int numProcs);
	 * 
	 * @param state
	 * @param pid
	 * @param arguments
	 * @param argumentValues
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private BooleanExpression guardOfWaitall(State state, int pid,
			Expression[] arguments, SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression procsPointer = argumentValues[0];
		SymbolicExpression numOfProcs = argumentValues[1];
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		IntegerNumber number_nprocs = (IntegerNumber) reasoner
				.extractNumber((NumericExpression) numOfProcs);
		String process = state.getProcessState(pid).name() + "(id=" + pid + ")";

		if (number_nprocs == null) {
			this.errorLogger.logSimpleError(arguments[1].getSource(), state,
					process, symbolicAnalyzer.stateInformation(state),
					ErrorKind.OTHER, "the number of processes for $waitall "
							+ "needs a concrete value");
			throw new UnsatisfiablePathConditionException();
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
						pointerAdd, procPointer, false);
				proc = eval.value;
				state = eval.state;
				pidValue = modelFactory.getProcessId(procsSource, proc);
				if (!modelFactory.isProcessIdNull(pidValue)
						&& modelFactory.isPocessIdDefined(pidValue))
					if (!state.getProcessState(pidValue).hasEmptyStack())
						return this.falseValue;
			}
		}
		return this.trueValue;
	}
}
