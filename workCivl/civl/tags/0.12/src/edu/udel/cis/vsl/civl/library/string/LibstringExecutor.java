/**
 * 
 */
package edu.udel.cis.vsl.civl.library.string;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.IF.BaseLibraryExecutor;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
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
import edu.udel.cis.vsl.sarl.IF.expr.ArrayElementReference;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicSequence;

/**
 * Executor for stdlib function calls.
 * 
 * @author Manchun Zheng (zmanchun)
 * @author zirkel
 * 
 */
public class LibstringExecutor extends BaseLibraryExecutor implements
		LibraryExecutor {

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
	public LibstringExecutor(String name, Executor primaryExecutor,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			CIVLConfiguration civlConfig) {
		super(name, primaryExecutor, modelFactory, symbolicUtil, civlConfig);
	}

	/* ******************** Methods from LibraryExecutor ******************* */

	@Override
	public State execute(State state, int pid, CallOrSpawnStatement statement)
			throws UnsatisfiablePathConditionException {
		return executeWork(state, pid, statement);
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
	private State executeWork(State state, int pid, CallOrSpawnStatement call)
			throws UnsatisfiablePathConditionException {
		Identifier name;
		Expression[] arguments;
		SymbolicExpression[] argumentValues;
		int numArgs;
		int processIdentifier = state.getProcessState(pid).identifier();
		String process = "p" + processIdentifier + " (id = " + pid + ")";
		LHSExpression lhs = call.lhs();

		numArgs = call.arguments().size();
		name = call.function().name();
		arguments = new Expression[numArgs];
		argumentValues = new SymbolicExpression[numArgs];
		for (int i = 0; i < numArgs; i++) {
			Evaluation eval;

			arguments[i] = call.arguments().get(i);
			eval = evaluator.evaluate(state, pid, arguments[i]);
			argumentValues[i] = eval.value;
			state = eval.state;
		}
		switch (name.name()) {
		case "strcpy":
			state = execute_strcpy(state, pid, process, lhs, arguments,
					argumentValues, call.getSource());
			break;
		case "strlen":
			state = execute_strlen(state, pid, process, lhs, arguments,
					argumentValues, call.getSource());
			break;
		default:
			throw new CIVLInternalException("Unknown stdlib function: " + name,
					call);
		}
		state = stateFactory.setLocation(state, pid, call.target());
		return state;
	}

	private State execute_strcpy(State state, int pid, String process,
			LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		Evaluation eval;
		SymbolicExpression charPointer = argumentValues[1];
		int startIndex;
		int lStartIndex;
		SymbolicExpression lhsPointer = symbolicUtil.parentPointer(source,
				argumentValues[0]);
		SymbolicSequence<?> originalArray;
		int numChars;
		int vid = symbolicUtil.getVariableId(source, lhsPointer);
		int scopeId = symbolicUtil.getDyscopeId(source, lhsPointer);
		ReferenceExpression symRef = symbolicUtil.getSymRef(lhsPointer);

		if (charPointer.operator() == SymbolicOperator.CONCRETE)
			startIndex = symbolicUtil.getArrayIndex(source, charPointer);
		else
			throw new CIVLUnimplementedFeatureException("non-concrete strings",
					source);
		if (lhsPointer.operator() == SymbolicOperator.CONCRETE)
			lStartIndex = symbolicUtil.getArrayIndex(source, lhsPointer);
		else
			throw new CIVLUnimplementedFeatureException("non-concrete strings",
					source);
		if (charPointer.type() instanceof SymbolicArrayType) {
			originalArray = (SymbolicSequence<?>) charPointer.argument(0);
		} else {
			SymbolicExpression arrayPointer = symbolicUtil.parentPointer(
					source, charPointer);
			ArrayElementReference arrayRef = (ArrayElementReference) symbolicUtil
					.getSymRef(charPointer);
			NumericExpression arrayIndex = arrayRef.getIndex();
			eval = evaluator.dereference(source, state, process, arrayPointer,
					false);

			state = eval.state;
			originalArray = (SymbolicSequence<?>) eval.value.argument(0);
			startIndex = symbolicUtil.extractInt(source, arrayIndex);
		}
		numChars = originalArray.size();
		for (int i = 0; i < numChars; i++) {
			SymbolicExpression charExpr = originalArray.get(i + startIndex);
			Character theChar = universe.extractCharacter(charExpr);
			ReferenceExpression eleRef = universe.arrayElementReference(symRef,
					universe.integer(i + lStartIndex));
			SymbolicExpression pointer = symbolicUtil.makePointer(scopeId, vid,
					eleRef);

			if (theChar == '\0')
				break;
			state = primaryExecutor.assign(source, state, process, pointer,
					charExpr);
		}
		if (lhs != null)
			state = primaryExecutor.assign(state, pid, process, lhs,
					argumentValues[0]);
		return state;
	}

	private State execute_strlen(State state, int pid, String process,
			LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		Evaluation eval;
		SymbolicExpression charPointer = argumentValues[0];
		int startIndex;
		SymbolicSequence<?> originalArray = null;
		int numChars;
		int length = 0;

		if (charPointer.operator() == SymbolicOperator.CONCRETE)
			startIndex = symbolicUtil.getArrayIndex(source, charPointer);
		else
			throw new CIVLUnimplementedFeatureException("non-concrete strings",
					source);
		if (charPointer.type() instanceof SymbolicArrayType) {
			originalArray = (SymbolicSequence<?>) charPointer.argument(0);
		} else {
			SymbolicExpression arrayPointer = symbolicUtil.parentPointer(
					source, charPointer);
			ArrayElementReference arrayRef = (ArrayElementReference) symbolicUtil
					.getSymRef(charPointer);
			NumericExpression arrayIndex = arrayRef.getIndex();
			eval = evaluator.dereference(source, state, process, arrayPointer,
					false);
			int numOfArgs;

			state = eval.state;
			numOfArgs  = eval.value.numArguments();
			
			for(int i = 0; i < numOfArgs; i++){
				if( eval.value.argument(i) instanceof SymbolicSequence<?>){
					originalArray = (SymbolicSequence<?>) eval.value.argument(i);
					break;
				}
			}
			startIndex = symbolicUtil.extractInt(source, arrayIndex);
		}
		numChars = originalArray.size();
		for (int i = 0; i < numChars-startIndex; i++) {
			SymbolicExpression charExpr = originalArray.get(i + startIndex);
			Character theChar = universe.extractCharacter(charExpr);
			
			if (theChar == '\0')
				break;
			length++;
		}
		if (lhs != null)
			state = primaryExecutor.assign(state, pid, process, lhs,
					universe.integer(length));
		return state;
	}
}
