package edu.udel.cis.vsl.civl.library.stdio;

import java.io.PrintStream;
import java.util.ArrayList;

import edu.udel.cis.vsl.civl.err.CIVLInternalException;
import edu.udel.cis.vsl.civl.err.CIVLSyntaxException;
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
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.expr.ArrayElementReference;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicSequence;

/**
 * Executor for stdio function calls. Some methods may be used elsewhere so this
 * executor may be loaded even if the user program has not included stdio. (See
 * "Other Public Methods".)
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

	/* *************************** Private Methods ************************* */

	/**
	 * Given a pointer to char, returns the array of char which is the string
	 * pointed to.
	 * 
	 * @param state
	 * @param source
	 * @param charPointer
	 * @return
	 */
	private SymbolicExpression getString(State state, CIVLSource source,
			SymbolicExpression charPointer) {
		BooleanExpression pc = state.getPathCondition();
		Reasoner reasoner = universe.reasoner(pc);
		// SymbolicExpression parentPointer = evaluator.parentPointer(source,
		// charPointer);
		ReferenceExpression symRef = evaluator.getSymRef(charPointer);

		// ReferenceKind kind = symRef.referenceKind();

		if (symRef.isArrayElementReference()) {
			ArrayElementReference arrayEltRef = (ArrayElementReference) symRef;
			NumericExpression indexExpr = arrayEltRef.getIndex();
			// try to get a concrete value
			int index;

			if (indexExpr.isZero()) {
				index = 0;
			} else {
				IntegerNumber indexNum = (IntegerNumber) reasoner
						.extractNumber(indexExpr);

				if (indexNum == null) {
					throw new CIVLUnimplementedFeatureException(
							"non-concrete symbolic index into string", source);
				} else {
					index = indexNum.intValue();
				}
			}
			if (index == 0) {
				// if this is a concrete array , find first occurrence of \0
				// else just take the whole array
			}
		}
		return null;

	}

	/**
	 * <pre>
	 * FILE *fopen(const char * restrict filename, const char * restrict mode);
	 * </pre>
	 * 
	 */
	private State executeOpen(State state, int pid, Expression[] expressions,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {

		return null;

	}

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
		// create abstract functions
		// create stdout, stdin
		return state;
	}

	@Override
	public State wrapUp(State state) {
		return state;
	}

	/* ************************ Other Public Methods *********************** */

	/**
	 * Execute <code>printf()</code> function. See C11 Sec. 7.21.6.1 and
	 * 7.21.6.3. Prototype:
	 * 
	 * <pre>
	 * int printf(const char * restrict format, ...);
	 * </pre>
	 * 
	 * Escape characters can be supported; the following have been tested:
	 * <code>\n</code>, <code>\r</code>, <code>\b</code>, <code>\t</code>,
	 * <code>\"</code>, <code>\'</code>, and <code>\\</code>. Some (but not all)
	 * format specifiers can be supported and the following have been tested:
	 * <code>%d</code>, <code>%o</code>, <code>%x</code>, <code>%f</code>,
	 * <code>%e</code>, <code>%g</code>, <code>%a</code>, <code>%c</code>,
	 * <code>%p</code>, and <code>%s</code>.
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
	public State executePrintf(State state, int pid, Expression[] expressions,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		if (this.enablePrintf) {
			// TODO: use StringBuffer instead for performance
			String stringOfSymbolicExpression = "";
			String format = "";
			ArrayList<String> arguments = new ArrayList<String>();
			CIVLSource source = state.getProcessState(pid).getLocation()
					.getSource();

			// don't assume argumentValues[0] is a pointer to an element of an
			// array. Check it. If it is not, through an exception.
			SymbolicExpression arrayPointer = evaluator.parentPointer(source,
					argumentValues[0]);
			Evaluation eval = evaluator
					.dereference(source, state, arrayPointer);

			if (eval.value.operator() != SymbolicOperator.CONCRETE)
				throw new CIVLUnimplementedFeatureException(
						"non-concrete format strings",
						expressions[0].getSource());

			SymbolicSequence<?> originalArray = (SymbolicSequence<?>) eval.value
					.argument(0);

			state = eval.state;
			
			int numChars = originalArray.size();
			char[] formatChars = new char[numChars];
			
			for (int i = 0; i < originalArray.size(); i++) {
				SymbolicExpression charExpr = originalArray.get(i);
				Character theChar = universe.extractCharacter(charExpr);

				if (theChar == null)
					throw new CIVLUnimplementedFeatureException(
							"non-concrete character in format string at position "
									+ i, expressions[0].getSource());

				formatChars[i] = theChar;
			}
			format = new String(formatChars);
			for (int i = 1; i < argumentValues.length; i++) {
				SymbolicExpression argument = argumentValues[i];
				CIVLType argumentType = expressions[i].getExpressionType();

				if (argumentType instanceof CIVLPointerType
						&& ((CIVLPointerType) argumentType).baseType()
								.isCharType()
						&& argument.operator() == SymbolicOperator.CONCRETE) {
					// also check format code is %s before doing this!
					arrayPointer = evaluator.parentPointer(source, argument);
					
					// index is not necessarily 0!  FIX ME!
					
					eval = evaluator.dereference(source, state, arrayPointer);
					originalArray = (SymbolicSequence<?>) eval.value
							.argument(0);
					state = eval.state;
					stringOfSymbolicExpression = "";
					
					// fix this way of making the string:
					
					for (int j = 0; j < originalArray.size(); j++) {
						stringOfSymbolicExpression += originalArray.get(j)
								.toString().charAt(1);
					}
					arguments.add(stringOfSymbolicExpression);
				} else
					arguments.add(argument.toString());
			}
			
			// TODO: print pointers in a much nicer way
			
			// TODO: at model building time, check statically that the
			// expression types are compatible with corresponding conversion
			// specifiers
			format = format.replaceAll("%lf", "%s");
			format = format.replaceAll("%[0-9]*[.]?[0-9]*[dfoxegacp]", "%s");
			for (int i = 0; i < format.length(); i++) {
				if (format.charAt(i) == '%') {
					if (format.charAt(i + 1) != 's')
						throw new CIVLSyntaxException("The format:%"
								+ format.charAt(i + 1)
								+ " is not allowed in printf",
								expressions[0].getSource());
				}
			}
			try {
				output.printf(format, arguments.toArray());
			} catch (Exception e) {
				throw new CIVLInternalException("unexpected error in printf",
						expressions[0].getSource());
			}
		}
		return state;
	}

}
