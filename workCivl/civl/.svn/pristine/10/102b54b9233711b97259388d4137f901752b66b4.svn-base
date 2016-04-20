package edu.udel.cis.vsl.civl.library.stdio;

import java.io.PrintStream;
import java.util.Vector;

import edu.udel.cis.vsl.civl.err.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.err.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.library.CommonLibraryExecutor;
import edu.udel.cis.vsl.civl.library.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPointerType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.semantics.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicSequence;

/**
 * Executor for stdio function calls.
 * 
 * @author Ziqing Luo (ziqing)
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class LibstdioExecutor extends CommonLibraryExecutor implements
		LibraryExecutor {

	/* **************************** Constructors *************************** */

	/**
	 * Create a new instance of library executor for "stdio.h".
	 * 
	 * @param primaryExecutor
	 *            The main executor of the system.
	 * @param output
	 *            The output stream for printing.
	 * @param enablePrintf
	 *            True iff print is enabled, reflecting command line options.
	 */
	public LibstdioExecutor(Executor primaryExecutor, PrintStream output,
			boolean enablePrintf, ModelFactory modelFactory) {
		super(primaryExecutor, output, enablePrintf, modelFactory);
	}

	/* ************************ Methods from Library *********************** */

	@Override
	public String name() {
		return "stdio";
	}

	/* ******************** Methods from LibraryExecutor ******************* */

	@Override
	public State execute(State state, int pid, CallOrSpawnStatement statement)
			throws UnsatisfiablePathConditionException {
		return executeWork(state, pid, (CallOrSpawnStatement) statement);
	}

	@Override
	public State initialize(State state) {
		return state;
	}

	@Override
	public State wrapUp(State state) {
		return state;
	}

	/* *************************** Private Methods ************************* */

	/**
	 * Execute a function call statement for a certain process at a given state.
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The Id of the process that the call statement belongs to.
	 * @param statement
	 *            The call statement to be executed.
	 * @return The new state after executing the call statement.
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeWork(State state, int pid,
			CallOrSpawnStatement statement)
			throws UnsatisfiablePathConditionException {
		Identifier name;
		Expression[] arguments;
		SymbolicExpression[] argumentValues;
		int numArgs;

		statement = (CallOrSpawnStatement) statement;
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
		case "printf":
			state = executePrintf(state, pid, arguments, argumentValues);
			state = stateFactory.setLocation(state, pid, statement.target());
			break;
		default:
			throw new CIVLUnimplementedFeatureException(name.name(), statement);

		}
		return state;
	}

	/**
	 * Execute Printf() function. Escape Characters can be supported and have
	 * been tested are: \n, \r, \b, \t, \", \', \\ Format specifiers can be
	 * supported and have been tested are: %d, %o, %x, %f, %e, %g, %a, %c, %s If
	 * users want to print addresses of pointers with arguments in the form of
	 * &a, please use %s as their format specifiers.
	 * 
	 * TODO CIVL currently dosen't support 'printf("%c" , c)'(where c is a char
	 * type variable)?
	 * 
	 * 
	 * @param state
	 * @param pid
	 * @param argumentValues
	 * @return State
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executePrintf(State state, int pid, Expression[] expressions,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		String stringOfSymbolicExpression = "";
		String format = "";
		Vector<Object> arguments = new Vector<Object>();
		CIVLSource source = state.getProcessState(pid).getLocation()
				.getSource();
		SymbolicExpression arrayPointer = evaluator.parentPointer(source,
				argumentValues[0]);
		Evaluation eval = evaluator.dereference(source, state, arrayPointer);
		SymbolicSequence<?> originalArray = (SymbolicSequence<?>) eval.value
				.argument(0);

		state = eval.state;
		if (!this.enablePrintf)
			return state;
		for (int i = 0; i < originalArray.size(); i++) {
			char current = originalArray.get(i).toString().charAt(1);

			if (current == '\u0007')
				throw new CIVLUnimplementedFeatureException("Escape sequence "
						+ current, source);
			format += current;
		}
		// obtain printf() arguments
		// stringOfSymbolicExpression += argumentValues[0];
		// format = stringOfSymbolicExpression;
		for (int i = 1; i < argumentValues.length; i++) {
			SymbolicExpression argument = argumentValues[i];
			CIVLType argumentType = expressions[i].getExpressionType();

			if ((argumentType instanceof CIVLPointerType)
					&& ((CIVLPointerType) argumentType).baseType().isCharType()
					&& argument.operator() == SymbolicOperator.CONCRETE) {
				arrayPointer = evaluator.parentPointer(source, argument);
				eval = evaluator.dereference(source, state, arrayPointer);
				originalArray = (SymbolicSequence<?>) eval.value.argument(0);
				state = eval.state;
				stringOfSymbolicExpression = "";
				for (int j = 0; j < originalArray.size(); j++) {
					stringOfSymbolicExpression += originalArray.get(j)
							.toString().charAt(1);
				}
				arguments.add(stringOfSymbolicExpression);
			} else
				arguments.add(argument.toString());
		}
		// Print
		format = format.replaceAll("%[0-9]*[.]?[0-9]*[dfoxegacp]", "%s");
		output.printf(format, arguments.toArray());
		return state;
	}

}
