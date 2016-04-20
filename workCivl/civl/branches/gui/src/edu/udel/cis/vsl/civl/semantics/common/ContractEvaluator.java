package edu.udel.cis.vsl.civl.semantics.common;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.mpi.LibmpiEvaluator;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.SystemFunction;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression.ExpressionKind;
import edu.udel.cis.vsl.civl.model.IF.expression.SystemFunctionCallExpression;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryLoaderException;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.MemoryUnitFactory;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;

public class ContractEvaluator extends CommonEvaluator implements Evaluator {

	public ContractEvaluator(ModelFactory modelFactory,
			StateFactory stateFactory, LibraryEvaluatorLoader loader,
			SymbolicUtility symbolicUtil, SymbolicAnalyzer symbolicAnalyzer,
			MemoryUnitFactory memUnitFactory, CIVLErrorLogger errorLogger,
			CIVLConfiguration config) {
		super(modelFactory, stateFactory, loader, symbolicUtil,
				symbolicAnalyzer, memUnitFactory, errorLogger, config);
	}

	@Override
	public Evaluation evaluate(State state, int pid, Expression expression,
			boolean checkUndefinedValue)
			throws UnsatisfiablePathConditionException {
		ExpressionKind kind = expression.expressionKind();

		if (kind.equals(ExpressionKind.SYSTEM_FUNC_CALL)) {
			int processIdentifier = state.getProcessState(pid).identifier();
			String process = "p" + processIdentifier + " (id = " + pid + ")";
			LibmpiEvaluator libevaluator;
			SystemFunctionCallExpression systemCallExpr = (SystemFunctionCallExpression) expression;
			Evaluation eval;
			String library;

			library = ((SystemFunction) systemCallExpr.callStatement()
					.function()).getLibrary();
			try {
				libevaluator = (LibmpiEvaluator) this.libLoader
						.getLibraryEvaluator(library, this, modelFactory,
								symbolicUtil, symbolicAnalyzer);
				eval = libevaluator.evaluateMPISystemFunctionCallExpression(
						state, pid, process,
						(SystemFunctionCallExpression) expression);
				return eval;
			} catch (LibraryLoaderException e) {
				StringBuffer message = new StringBuffer();
				CIVLFunction function = ((SystemFunctionCallExpression) expression)
						.callStatement().function();

				message.append("unable to load the library evaluator for the library ");
				message.append(library);
				message.append(" for the function ");
				message.append(function);
				errorLogger.logSimpleError(expression.getSource(), state,
						process, this.symbolicAnalyzer.stateInformation(state),
						ErrorKind.LIBRARY, message.toString());
				return new Evaluation(state, universe.falseExpression());
			}
		} else
			return super.evaluate(state, pid, expression, checkUndefinedValue);
	}
}
