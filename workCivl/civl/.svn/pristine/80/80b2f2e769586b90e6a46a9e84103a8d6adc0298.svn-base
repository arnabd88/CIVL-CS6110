/**
 * 
 */
package edu.udel.cis.vsl.civl.library.string;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.bundle.LibbundleEvaluator;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryExecutor;
import edu.udel.cis.vsl.civl.log.IF.CIVLExecutionException;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.Certainty;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
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
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryLoaderException;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.civl.util.IF.Triple;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.ArrayElementReference;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicFunctionType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicSequence;
import edu.udel.cis.vsl.sarl.ideal.common.IdealSymbolicConstant;

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
			SymbolicAnalyzer symbolicAnalyzer, CIVLConfiguration civlConfig,
			LibraryExecutorLoader libExecutorLoader,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, primaryExecutor, modelFactory, symbolicUtil,
				symbolicAnalyzer, civlConfig, libExecutorLoader,
				libEvaluatorLoader);
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
		case "strcmp":
			state = execute_strcmp(state, pid, process, lhs, arguments,
					argumentValues, call.getSource());
			break;
		case "memset":
			state = execute_memset(state, pid, process, lhs, arguments,
					argumentValues, call.getSource());
			break;
		default:
			throw new CIVLInternalException("Unknown string function: " + name,
					call);
		}
		state = stateFactory.setLocation(state, pid, call.target(),
				call.lhs() != null);
		return state;
	}

	// TODO: this function assume the "lhsPointer" which is argument[0] is a
	// pointer to heap object element which needs being improved.
	private State execute_strcpy(State state, int pid, String process,
			LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		Evaluation eval;
		SymbolicExpression charPointer = argumentValues[1];
		int startIndex;
		int lStartIndex;
		SymbolicExpression lhsPointer = argumentValues[0];
		// symbolicUtil.parentPointer(source, argumentValues[0]);
		SymbolicSequence<?> originalArray;
		int numChars;
		int vid = symbolicUtil.getVariableId(source, lhsPointer);
		int scopeId = symbolicUtil.getDyscopeId(source, lhsPointer);
		ReferenceExpression symRef = ((ArrayElementReference) symbolicUtil
				.getSymRef(lhsPointer)).getParent();

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
			// TODO: implement getStringConcrete() as an underneath
			// implementation of getString()
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

	/**
	 * <code>int strcmp(const char * s1, const char * s2)</code> Compare two
	 * strings s1 and s2. Return 0 if s1 = s2. If s1 > s2, return a value
	 * greater than 0 and if s1 < s2, return a value less than zero. <br>
	 * Comparison:<br>
	 * The comparison is determined by the sign of the difference between the
	 * values of the first pair of characters (both interpreted as unsigned
	 * char) that differ in the objects being compared.
	 * 
	 * @param state
	 *            the current state
	 * @param pid
	 *            the PID of the process
	 * @param process
	 *            the information of the process
	 * @param lhs
	 *            the expression of the left-hand side variable
	 * @param arguments
	 *            the expressions of arguments
	 * @param argumentValues
	 *            the symbolic expressions of arguments
	 * @param source
	 *            the CIVL source of the statement
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State execute_strcmp(State state, int pid, String process,
			LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		int output = 0;
		NumericExpression result;
		SymbolicExpression charPointer1 = argumentValues[0];
		SymbolicExpression charPointer2 = argumentValues[1];
		Triple<State, StringBuffer, Boolean> strEval1 = null;
		Triple<State, StringBuffer, Boolean> strEval2 = null;
		StringBuffer str1, str2;

		if ((charPointer1.operator() != SymbolicOperator.CONCRETE))
			errorLogger.reportError(new CIVLExecutionException(
					ErrorKind.POINTER, Certainty.CONCRETE, process,
					"Attempt to read/write from an invalid pointer\n",
					arguments[0].getSource()));
		if ((charPointer2.operator() != SymbolicOperator.CONCRETE))
			errorLogger.reportError(new CIVLExecutionException(
					ErrorKind.POINTER, Certainty.CONCRETE, process,
					"Attempt to read/write from an invalid pointer\n",
					arguments[1].getSource()));
		// If two pointers are same, return 0.
		if (charPointer1.equals(charPointer2))
			result = zero;
		else {
			try {
				strEval1 = evaluator.getString(source, state, process,
						charPointer1);
				state = strEval1.first;
				strEval2 = evaluator.getString(source, state, process,
						charPointer2);
				state = strEval2.first;
			} catch (CIVLExecutionException e) {
				errorLogger.reportError(new CIVLExecutionException(e.kind(), e
						.certainty(), process, e.getMessage(), source));
			} catch (Exception e) {
				throw new CIVLInternalException("Unknown error", source);
			}

			if (!strEval1.third || !strEval2.third) {

				// catch (CIVLUnimplementedFeatureException e) {
				// If the string pointed by either pointer1 or pointer2 is
				// non-concrete, try to compare two string objects, if
				// different, return abstract function.
				SymbolicExpression symResult;
				SymbolicExpression strObj1, strObj2;
				Evaluation eval;

				eval = evaluator.dereference(arguments[0].getSource(), state,
						process, charPointer1, true);
				state = eval.state;
				strObj1 = eval.value;
				eval = evaluator.dereference(arguments[1].getSource(), state,
						process, charPointer2, true);
				state = eval.state;
				strObj2 = eval.value;
				if (strObj1.equals(strObj2))
					symResult = zero;
				else {
					SymbolicFunctionType funcType;
					SymbolicExpression func;

					funcType = universe.functionType(
							Arrays.asList(charPointer1.type(),
									charPointer2.type()),
							universe.integerType());
					func = universe.canonic(universe.symbolicConstant(
							universe.stringObject("strcmp"), funcType));
					symResult = universe.apply(func,
							Arrays.asList(charPointer1, charPointer2));
				}
				if (lhs != null)
					state = primaryExecutor.assign(state, pid, process, lhs,
							symResult);
				return state;
			} else {
				assert (strEval1.second != null && strEval2.second != null) : "Evaluating String failed";
				str1 = strEval1.second;
				str2 = strEval2.second;
				output = str1.toString().compareTo(str2.toString());
				result = universe.integer(output);
			}
		}
		if (lhs != null)
			state = primaryExecutor.assign(state, pid, process, lhs, result);
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
			numOfArgs = eval.value.numArguments();

			for (int i = 0; i < numOfArgs; i++) {
				if (eval.value.argument(i) instanceof SymbolicSequence<?>) {
					originalArray = (SymbolicSequence<?>) eval.value
							.argument(i);
					break;
				}
			}
			startIndex = symbolicUtil.extractInt(source, arrayIndex);
		}
		numChars = originalArray.size();
		for (int i = 0; i < numChars - startIndex; i++) {
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

	/**
	 * Execute memset() function. CIVL currently only support set memory units
	 * to zero (In other words, the second argument of the memset function can
	 * only be zero).
	 * 
	 * @param state
	 *            the current state
	 * @param pid
	 *            the PID of the process
	 * @param process
	 *            the identifier of the process
	 * @param lhs
	 *            the left hand size expression
	 * @param arguments
	 *            the expressions of arguments
	 * @param argumentValues
	 *            the symbolic expressions of arguments
	 * @param source
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 * @author ziqing luo
	 */
	private State execute_memset(State state, int pid, String process,
			LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression pointer, c;
		NumericExpression size, length, dataTypeSize;
		SymbolicExpression zerosArray;
		SymbolicExpression zeroVar;
		SymbolicType objectElementType;
		BooleanExpression claim;
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		ResultType resultType;
		Evaluation eval;
		LibbundleEvaluator libEvaluator;
		Pair<Evaluation, ArrayList<NumericExpression>> ptrAddRet;
		Pair<Evaluation, SymbolicExpression> setDataRet;
		edu.udel.cis.vsl.sarl.IF.number.Number num_length;
		int int_length;
		boolean byteIsUnit = true;

		pointer = argumentValues[0];
		c = argumentValues[1];
		// check if pointer is valid first
		if (pointer.operator() != SymbolicOperator.CONCRETE)
			errorLogger.reportError(new CIVLExecutionException(
					ErrorKind.POINTER, Certainty.CONCRETE, process,
					"Attempt to read/write from an invalid pointer\n",
					arguments[0].getSource()));
		// check if c == 0, because that's the only case we support
		claim = universe.equals(c, zero);
		resultType = reasoner.valid(claim).getResultType();
		if (resultType != ResultType.YES) {
			throw new CIVLUnimplementedFeatureException(
					"memset() is not support copy a non-zero: " + c
							+ " value to the given address");
		}
		size = (NumericExpression) argumentValues[2];
		objectElementType = symbolicAnalyzer.getFlattenedArrayElementType(
				state, arguments[0].getSource(), pointer).getDynamicType(
				universe);
		dataTypeSize = symbolicUtil.sizeof(arguments[0].getSource(),
				objectElementType);
		for (SymbolicObject obj : size.arguments()) {
			if (obj instanceof IdealSymbolicConstant) {
				/*
				 * size contains any "SIZEOF(CHAR) or SIZEOF(BOOLEAN)", never
				 * simplify SIZEOF(CHAR)(or SIZEOF(BOOLEAN) to one
				 */
				if (obj.equals(symbolicUtil.sizeof(null,
						universe.characterType()))
						|| obj.equals(symbolicUtil.sizeof(null,
								universe.booleanType())))
					byteIsUnit = false;
			}
		}
		switch (objectElementType.typeKind()) {
		case REAL:
			zeroVar = universe.rational(0);
			break;
		case INTEGER:
			zeroVar = universe.integer(0);
			break;
		case CHAR:
			zeroVar = universe.character('\0');
			if (byteIsUnit)
				dataTypeSize = one;
			break;
		case BOOLEAN:
			zeroVar = universe.bool(false);
			if (byteIsUnit)
				dataTypeSize = one;
			break;
		default:
			throw new CIVLUnimplementedFeatureException(
					"Any datatype other than REAL, INTEGER, CHAR and BOOLEAN is not supported yet");
		}
		length = universe.divide(size, dataTypeSize);
		ptrAddRet = evaluator.evaluatePointerAdd(state, process, pointer,
				length, false, arguments[0].getSource());
		eval = ptrAddRet.left;
		state = eval.state;
		// create a set of zeros to set to the pointed object.
		num_length = universe.extractNumber(length);
		if (num_length != null) {
			List<SymbolicExpression> zeros = new LinkedList<>();

			int_length = ((IntegerNumber) num_length).intValue();
			for (int i = 0; i < int_length; i++)
				zeros.add(zeroVar);
			zerosArray = universe.array(objectElementType, zeros);
		} else {
			zerosArray = symbolicUtil.newArray(state.getPathCondition(),
					objectElementType, length, zeroVar);
		}
		// Calling setDataFrom to set the pointed object to zero
		try {
			libEvaluator = (LibbundleEvaluator) this.libEvaluatorLoader
					.getLibraryEvaluator("bundle", evaluator, modelFactory,
							symbolicUtil, symbolicAnalyzer);
			setDataRet = libEvaluator.setDataFrom(state, process, pointer,
					length, zerosArray, false, source);
			eval = setDataRet.left;
			state = eval.state;
			state = this.primaryExecutor.assign(source, state, process,
					setDataRet.right, eval.value);
		} catch (LibraryLoaderException e) {
			throw new CIVLInternalException(
					"Failure of loading library evaluator of library 'string'",
					source);
		}
		if (lhs != null) {
			state = primaryExecutor.assign(state, pid, process, lhs, pointer);
		}
		return state;
	}
}
