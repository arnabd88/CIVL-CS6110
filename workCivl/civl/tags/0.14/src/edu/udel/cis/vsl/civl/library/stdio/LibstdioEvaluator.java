package edu.udel.cis.vsl.civl.library.stdio;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryEvaluator;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicFunctionType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class LibstdioEvaluator extends BaseLibraryEvaluator implements
		LibraryEvaluator {

	public LibstdioEvaluator(String name, Evaluator evaluator,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, evaluator, modelFactory, symbolicUtil, symbolicAnalyzer,
				libEvaluatorLoader);
	}

	/**
	 * Similar to the function
	 * {@link edu.udel.cis.vsl.civl.library.bundle.LibbundleEvaluator#setDataFrom(State, String, SymbolicExpression, NumericExpression, SymbolicExpression, boolean, CIVLSource) 
	 * }
	 * Set a sequence of data to an object pointed by the given pointer.
	 * 
	 * 
	 * @param state
	 *            The current state
	 * @param process
	 *            The information of the process
	 * @param data
	 *            The data will be set to an object.
	 * @param argPtr
	 *            The pointer to the object which will be updated by "data"
	 * @param offset
	 *            The length of the data which should be guaranteed be in form
	 *            of an 1-d array.
	 * @param source
	 *            The CIVL Source of the statement.
	 * @return The Evaluation contains the new object and a corresponding
	 *         pointer which can be either an ancestor of the given pointer or
	 *         the given pointer itself. Similar return type as
	 *         {@link edu.udel.cis.vsl.civl.library.bundle.LibbundleEvaluator#setDataFrom(State, String, SymbolicExpression, NumericExpression, SymbolicExpression, boolean, CIVLSource)}
	 * @throws UnsatisfiablePathConditionException
	 */
	Pair<Evaluation, SymbolicExpression> setOutputArgument(State state,
			String process, SymbolicExpression data, SymbolicExpression argPtr,
			NumericExpression offset, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression endPtr;
		Pair<Evaluation, Map<Integer, NumericExpression>> eval_and_arrayInfo;
		Evaluation eval;

		eval_and_arrayInfo = evaluator.evaluatePointerAdd(state, process,
				argPtr, universe.subtract(offset, one), false, source);
		eval = eval_and_arrayInfo.left;
		state = eval.state;
		endPtr = eval.value;
		if (eval_and_arrayInfo.right == null) {
			eval_and_arrayInfo.right = new HashMap<>();
			eval_and_arrayInfo.right.put(0, one);
		}
		return this.setDataBetween(state, process, argPtr, endPtr, data,
				eval_and_arrayInfo.right, source);
	}

	/**
	 * Create a symbolic string constant which essentially is an array of
	 * characters.
	 * 
	 * @param arrayLength
	 *            The length of the array of characters or number of characters
	 *            in the generating string.
	 * @return The symbolic string constant
	 */
	SymbolicConstant charsToString(NumericExpression arrayLength) {
		SymbolicType charType = universe.characterType();
		SymbolicType arrayType = universe.arrayType(charType, arrayLength);
		SymbolicArrayType stringSymType = (SymbolicArrayType) universe
				.canonic(universe.arrayType(universe.characterType()));
		SymbolicFunctionType funcType = universe.functionType(
				Arrays.asList(stringSymType, stringSymType), arrayType);
		SymbolicConstant charsToString = (SymbolicConstant) universe
				.canonic(universe.symbolicConstant(
						universe.stringObject("charsToString"), funcType));
		return charsToString;
	}
}
