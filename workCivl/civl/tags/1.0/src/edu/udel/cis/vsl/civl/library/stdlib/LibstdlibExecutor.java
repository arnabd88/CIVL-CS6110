/**
 * 
 */
package edu.udel.cis.vsl.civl.library.stdlib;

import java.util.Arrays;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryExecutor;
import edu.udel.cis.vsl.civl.log.IF.CIVLExecutionException;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.Certainty;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Triple;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * Executor for stdlib function calls.
 * 
 * @author Manchun Zheng (zmanchun)
 * @author zirkel
 * 
 */
public class LibstdlibExecutor extends BaseLibraryExecutor implements
		LibraryExecutor {

	private SymbolicConstant atoiFunction;

	/* **************************** Constructors *************************** */

	/**
	 * Create a new instance of library executor for "stdlib.h".
	 * 
	 * @param primaryExecutor
	 *            The main executor of the system.
	 * @param output
	 *            The output stream for printing.
	 * @param enablePrintf
	 *            True iff print is enabled, reflecting command line options.
	 */
	public LibstdlibExecutor(String name, Executor primaryExecutor,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer, CIVLConfiguration civlConfig,
			LibraryExecutorLoader libExecutorLoader,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, primaryExecutor, modelFactory, symbolicUtil,
				symbolicAnalyzer, civlConfig, libExecutorLoader,
				libEvaluatorLoader);

		SymbolicType stringSymbolicType;
		stringSymbolicType = typeFactory.pointerType(typeFactory.charType())
				.getDynamicType(universe);
		atoiFunction = (SymbolicConstant) universe.canonic(universe
				.symbolicConstant(universe.stringObject("atoi"), universe
						.functionType(Arrays.asList(stringSymbolicType),
								universe.integerType())));
	}

	/* ******************** Methods from LibraryExecutor ******************* */

	@Override
	public State execute(State state, int pid, CallOrSpawnStatement statement,
			String functionName) throws UnsatisfiablePathConditionException {
		return executeWork(state, pid, statement, functionName);
	}

	/* *************************** Private Methods ************************* */

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
		int numArgs;
		String process = state.getProcessState(pid).name() + "(id=" + pid + ")";
		LHSExpression lhs = call.lhs();
		CIVLSource source = call.getSource();

		numArgs = call.arguments().size();
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
		case "free":
			state = executeFree(state, pid, process, arguments, argumentValues,
					call.getSource());
			break;
		case "atoi":
			state = execute_atoi(state, pid, process, lhs, arguments,
					argumentValues, source);
			break;
		default:
			throw new CIVLInternalException("Unknown stdlib function: " + name,
					call);
		}
		state = stateFactory.setLocation(state, pid, call.target(),
				call.lhs() != null);
		return state;
	}

	private State execute_atoi(State state, int pid, String process,
			LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression intValue = null;

		if (argumentValues[0].operator() != SymbolicOperator.CONCRETE) {
			intValue = universe.apply(atoiFunction,
					Arrays.asList(argumentValues[0]));
		} else {
			Triple<State, StringBuffer, Boolean> argStringPair = null;
			String argString;

			argStringPair = this.evaluator.getString(arguments[0].getSource(),
					state, process, argumentValues[0]);
			if (!argStringPair.third) {
				intValue = universe.apply(atoiFunction,
						Arrays.asList(argumentValues[0]));
			} else {
				// try {
				// argStringPair = this.evaluator.getString(
				// arguments[0].getSource(), state, process,
				// argumentValues[0]);
				// } catch (CIVLUnimplementedFeatureException e) {
				// intValue = universe.apply(atoiFunction,
				// Arrays.asList(argumentValues[0]));
				// }
				// if (argStringPair != null) {
				state = argStringPair.first;
				argString = argStringPair.second.toString();
				try {
					int integer = Integer.parseInt(argString);

					intValue = universe.integer(integer);
				} catch (Exception ex) {
					CIVLExecutionException e = new CIVLExecutionException(
							ErrorKind.OTHER, Certainty.PROVEABLE, process,
							"The argument to atoi() should be a valid integer representation.\n"
									+ "actual argument: " + argString,
							symbolicAnalyzer.stateInformation(state), source);

					errorLogger.reportError(e);
				}
			}
		}
		if (lhs != null && intValue != null)
			state = primaryExecutor.assign(state, pid, process, lhs, intValue);
		return state;
	}

}
