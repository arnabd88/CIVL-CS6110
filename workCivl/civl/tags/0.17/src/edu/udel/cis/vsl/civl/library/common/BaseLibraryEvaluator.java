package edu.udel.cis.vsl.civl.library.common;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.log.IF.CIVLExecutionException;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.Certainty;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SARLException;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * This class provides the common data and operations of library evaluators.
 * 
 * @author Manchun Zheng
 * 
 */
public abstract class BaseLibraryEvaluator extends LibraryComponent implements
		LibraryEvaluator {
	/**
	 * The evaluator for evaluating expressions.
	 */
	protected Evaluator evaluator;

	/**
	 * The model factory of the system.
	 */
	protected ModelFactory modelFactory;

	/**
	 * The state factory for state-related computation.
	 */
	protected StateFactory stateFactory;

	protected CIVLErrorLogger errorLogger;

	/* ***************************** Constructor *************************** */

	/**
	 * Creates a new instance of library enabler.
	 * 
	 * @param primaryEnabler
	 *            The enabler for normal CIVL execution.
	 * @param output
	 *            The output stream to be used in the enabler.
	 * @param modelFactory
	 *            The model factory of the system.
	 * @param symbolicUtil
	 *            The symbolic utility used in the system.
	 * @param symbolicAnalyzer
	 *            The symbolic analyzer used in the system.
	 */
	public BaseLibraryEvaluator(String name, Evaluator evaluator,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, evaluator.universe(), symbolicUtil, symbolicAnalyzer,
				libEvaluatorLoader);
		this.evaluator = evaluator;
		this.stateFactory = evaluator.stateFactory();
		this.modelFactory = modelFactory;
		this.errorLogger = evaluator.errorLogger();
	}

	/* ******************** Methods from LibraryEvaluator ****************** */

	@Override
	public Evaluation evaluateGuard(CIVLSource source, State state, int pid,
			String function, List<Expression> arguments)
			throws UnsatisfiablePathConditionException {
		return new Evaluation(state, universe.trueExpression());
	}

	/* ******************** Public Array Utility functions ****************** */
	/**
	 * Cast an array to another array. The two arrays before and after casting
	 * must be able to hold same number of non-array elements.<br>
	 * e.g. For arrays <code>int a[2][2]; int b[4]; int c[5]</code>, a and b can
	 * be casted into each other but both of them can not be casted to c.
	 * 
	 * @author Ziqing Luo
	 * @param state
	 *            The current state
	 * @param process
	 *            The information of the process
	 * @param oldArray
	 *            The array before casting
	 * @param targetTypeArray
	 *            The array has the type which is the target type of casting
	 * @param source
	 *            The CIVL source of the oldArray or the pointer to OldArray
	 * @return casted array
	 * @throws UnsatisfiablePathConditionException
	 */
	public SymbolicExpression arrayCasting(State state, String process,
			SymbolicExpression oldArray, SymbolicExpression targetTypeArray,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		BooleanExpression claim;
		NumericExpression extent, chunkLength, oldArraySize;
		List<SymbolicExpression> elements = new LinkedList<>();
		Reasoner reasoner = universe.reasoner(state.getPathCondition());

		if (!(oldArray.type() instanceof SymbolicCompleteArrayType))
			throw new CIVLInternalException(
					"Array casting cannot be applied on non-array type object or incomplete array",
					source);
		if (!(targetTypeArray.type() instanceof SymbolicCompleteArrayType))
			throw new CIVLInternalException(
					"Array casting cannot cast to non-array type object or incomplete array type",
					source);
		extent = universe.length(targetTypeArray);
		oldArraySize = universe.length(oldArray);
		chunkLength = universe.divide(oldArraySize, extent);
		if (reasoner.isValid(universe.equals(chunkLength, one))
				&& (!(((SymbolicArrayType) targetTypeArray.type())
						.elementType() instanceof SymbolicArrayType)))
			return oldArray;
		else {
			NumericExpression i = zero;
			NumericExpression endIndex = chunkLength;
			SymbolicExpression flattenOldArray = arrayFlatten(state, process,
					oldArray, source);

			if (!(((SymbolicArrayType) targetTypeArray.type()).elementType() instanceof SymbolicArrayType))
				throw new CIVLInternalException(
						"Array cannot be casted to an non-array type", source);
			claim = universe.lessThan(i, extent);
			while (reasoner.isValid(claim)) {
				SymbolicExpression subArray = symbolicAnalyzer.getSubArray(
						flattenOldArray, universe.multiply(i, chunkLength),
						endIndex, state, process, source);
				SymbolicExpression childArray;

				childArray = arrayCasting(state, process, subArray,
						universe.arrayRead(targetTypeArray, zero), source);

				elements.add(childArray);
				// update
				i = universe.add(i, one);
				endIndex = universe.add(endIndex, chunkLength);
				claim = universe.lessThan(i, extent);
			}
			return universe.array(elements.get(0).type(), elements);
		}
	}

	/**
	 * Flatten the given array. Here flatten means converting a nested array
	 * (which represents multiple dimensional array in CIVL) to an one
	 * dimensional array.
	 * 
	 * @param state
	 *            The current state
	 * @param process
	 *            The information of the process
	 * @param array
	 *            The array which is going to be flatten
	 * @param civlsource
	 *            The CIVL source the array or the pointer to the array
	 * @return the flatten array
	 * @throws UnsatisfiablePathConditionException
	 */
	public SymbolicExpression arrayFlatten(State state, String process,
			SymbolicExpression array, CIVLSource civlsource)
			throws UnsatisfiablePathConditionException {
		List<SymbolicExpression> flattenElementList;
		ArrayList<NumericExpression> arrayElementsSizes;
		Reasoner reasoner = universe.reasoner(state.getPathCondition());

		if (array == null)
			throw new CIVLInternalException("parameter 'array' is null.",
					civlsource);
		if (array.isNull())
			return array;
		// If the array is already a one-dimensional array no matter if the
		// length is concrete or non-concrete, return it directly.
		if (!(((SymbolicArrayType) array.type()).elementType() instanceof SymbolicArrayType))
			return array;
		// If the array has at least one dimension whose length is non-concrete,
		// using array lambda to flatten it.
		if (this.hasNonConcreteExtent(reasoner, array)) {
			arrayElementsSizes = symbolicUtil.getArrayElementsSizes(array,
					civlsource);
			return this.arrayLambdaFlatten(state, array, arrayElementsSizes,
					civlsource);
		}
		flattenElementList = this.arrayFlattenWorker(state, array, civlsource);
		if (flattenElementList.size() > 0) {
			assert (!(flattenElementList.get(0).type() instanceof SymbolicArrayType));
			return universe.array(flattenElementList.get(0).type(),
					flattenElementList);
		} else if (array instanceof SymbolicArrayType)
			return universe.emptyArray(((SymbolicArrayType) array)
					.elementType());
		else
			return universe.emptyArray(array.type());
	}

	/* ************* Output Argument Assignment Utility functions ************ */
	/*
	 * These utility functions are used for dealing with assigning objects to
	 * output arguments. Since this kind of assignment usually involves
	 * assigning a sequence of data to an object pointed by a pointer and some
	 * objects are represented differently in CIVL implementation from C
	 * language(e.g. Multi-dimensional arrays), following functions intend to be
	 * reused and make implementing those assignments more convenient.
	 */
	/**
	 * Setting a sequence of data between two array element references. Returns
	 * the settled new array and the pointer to that array.
	 * 
	 * Pre-condition: start pointer and end pointer should point to the same
	 * object.
	 * 
	 * @param state
	 *            The current state
	 * @param process
	 *            The information of the process
	 * @param startPtr
	 *            The pointer to the start position
	 * @param endPtr
	 *            The pointer to the end position
	 * @param dataArray
	 *            The sequence of data which is going to be set
	 * @param arrayElementsSizes
	 *            The capacity information of the array pointed by the startPtr
	 *            or endPtr(These two pointers point to the same object).<br>
	 *            Note: Here capacity information of an array means that for one
	 *            cell in each dimension of an array how many non-array elements
	 *            it can hold. e.g. For array <code>int a[2][2];</code>, the one
	 *            cell in deepest dimension can only hold one element while one
	 *            cell in the second deepest dimension can hold 2 elements. Here
	 *            we use 0 marking (which is key in the given map) the deepest
	 *            dimension and 1 marking the second deepest dimension and so
	 *            forth.
	 * @param source
	 *            The CIVL source of the start pointer.
	 * @return the settled new array and the pointer to that array.
	 * @throws UnsatisfiablePathConditionException
	 * @author Ziqing Luo
	 */
	public Pair<Evaluation, SymbolicExpression> setDataBetween(State state,
			String process, SymbolicExpression startPtr,
			SymbolicExpression endPtr, SymbolicExpression dataArray,
			ArrayList<NumericExpression> arrayElementsSizes, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression startPointer, endPointer;
		SymbolicExpression flattenLeastCommonArray, leastCommonArray;
		NumericExpression startPos = zero;
		NumericExpression endPos = zero;
		NumericExpression ptrInterval;
		NumericExpression dataSize;
		NumericExpression i, j;
		Evaluation eval;
		BooleanExpression claim;
		boolean sidMatch, vidMatch;
		int dim = 0;
		Map<Integer, NumericExpression> startIndexes;
		Map<Integer, NumericExpression> endIndexes;
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		ResultType resultType;

		// Checking if they are pointing to the same thing
		sidMatch = (symbolicUtil.getDyscopeId(source, startPtr) == symbolicUtil
				.getDyscopeId(source, endPtr));
		vidMatch = (symbolicUtil.getVariableId(source, startPtr) == symbolicUtil
				.getVariableId(source, endPtr));
		if (!(sidMatch && vidMatch))
			throw new CIVLInternalException("Object unmatch exception\n",
					source);
		startPointer = symbolicAnalyzer.castToArrayElementReference(state,
				startPtr, source);
		endPointer = symbolicAnalyzer.castToArrayElementReference(state,
				endPtr, source);
		startIndexes = symbolicAnalyzer.arrayIndexesByPointer(state, source,
				startPointer, false);
		endIndexes = symbolicAnalyzer.arrayIndexesByPointer(state, source,
				endPointer, false);
		while (!startPointer.equals(endPointer)) {
			startPos = universe.add(
					startPos,
					universe.multiply(startIndexes.get(dim),
							arrayElementsSizes.get(dim)));
			endPos = universe.add(
					endPos,
					universe.multiply(endIndexes.get(dim),
							arrayElementsSizes.get(dim)));
			dim++;
			startPointer = symbolicUtil.parentPointer(source, startPointer);
			endPointer = symbolicUtil.parentPointer(source, endPointer);
		}
		ptrInterval = universe.subtract(endPos, startPos);
		assert (reasoner.isValid(universe.lessThanEquals(zero, ptrInterval)));
		dim = 1;
		dataSize = universe.length(dataArray);
		claim = universe.lessThanEquals(dataSize,
				universe.add(ptrInterval, one));
		resultType = reasoner.valid(claim).getResultType();
		if (!resultType.equals(ResultType.YES))
			state = errorLogger
					.logError(
							source,
							state,
							process,
							symbolicAnalyzer.stateToString(state),
							claim,
							resultType,
							ErrorKind.OUT_OF_BOUNDS,
							"Array index out of bound when writing data into the object pointed by "
									+ symbolicAnalyzer
											.symbolicExpressionToString(source,
													state, startPtr)
									+ ".\n"
									+ "Number of elements in data: "
									+ dataSize
									+ ".\nNumber of elements can be stored in the object: "
									+ universe.add(ptrInterval, one) + ".\n");
		eval = evaluator.dereference(source, state, process, startPointer,
				false);
		state = eval.state;
		leastCommonArray = eval.value;
		// If the result of dereferencing is not an array type, then the
		// dataSize should only be one.
		if (!(leastCommonArray.type() instanceof SymbolicArrayType)) {
			claim = universe.equals(dataSize, one);
			resultType = reasoner.valid(claim).getResultType();
			if (!resultType.equals(ResultType.YES))
				state = errorLogger
						.logError(
								source,
								state,
								process,
								symbolicAnalyzer.stateToString(state),
								claim,
								resultType,
								ErrorKind.OUT_OF_BOUNDS,
								"Array index out of bound when unpacking bundle data into the object pointed by "
										+ symbolicAnalyzer
												.symbolicExpressionToString(
														source, state, startPtr)
										+ ".\n"
										+ "Number of elements in data: "
										+ dataSize
										+ ".\nNumber of elements can be stored in the object: 1\n");
			eval = new Evaluation(state, universe.arrayRead(dataArray, zero));
			return new Pair<>(eval, startPtr);
		}
		// Direct assignment conditions:
		// 1. start position is zero.
		// 2. Interval between pointers equals to data size.
		// 3. The least common array capacity equals to data size.
		if (reasoner.isValid(universe.equals(startPos, zero))) {
			NumericExpression arrayCapacity = this.arraySize(leastCommonArray,
					source);

			claim = universe.and(
					universe.equals(dataSize, universe.add(ptrInterval, one)),
					universe.equals(dataSize, arrayCapacity));
			if (reasoner.isValid(claim)) {
				dataArray = arrayCasting(state, process, dataArray,
						leastCommonArray, source);
				eval = new Evaluation(state, dataArray);
				return new Pair<Evaluation, SymbolicExpression>(eval,
						startPointer);
			}
		}
		flattenLeastCommonArray = arrayFlatten(state, process,
				leastCommonArray, source);
		i = startPos;
		j = zero;
		claim = universe.lessThan(j, dataSize);
		while (reasoner.isValid(claim)) {
			SymbolicExpression elementInDataArray = null;

			try {
				elementInDataArray = universe.arrayRead(dataArray, j);
			} catch (SARLException e) {
				CIVLExecutionException err = new CIVLExecutionException(
						ErrorKind.OUT_OF_BOUNDS, Certainty.CONCRETE, process,
						"Array index out of bound when reading data object "
								+ symbolicAnalyzer.symbolicExpressionToString(
										source, state, dataArray)
								+ " at position "
								+ symbolicAnalyzer.symbolicExpressionToString(
										source, state, startPtr)
								+ " + offset :" + j, source);

				errorLogger.reportError(err);
			}
			try {
				flattenLeastCommonArray = universe.arrayWrite(
						flattenLeastCommonArray, i, elementInDataArray);
			} catch (SARLException e) {
				CIVLExecutionException err = new CIVLExecutionException(
						ErrorKind.OUT_OF_BOUNDS, Certainty.CONCRETE, process,
						"Array index out of bound when writing object "
								+ symbolicAnalyzer.symbolicExpressionToString(
										source, state, leastCommonArray)
								+ " at position "
								+ symbolicAnalyzer.symbolicExpressionToString(
										source, state, startPtr)
								+ " + offset :" + i, source);

				errorLogger.reportError(err);
			}
			i = universe.add(i, one);
			j = universe.add(j, one);
			claim = universe.lessThan(j, dataSize);
		}

		flattenLeastCommonArray = arrayCasting(state, process,
				flattenLeastCommonArray, leastCommonArray, source);
		eval = new Evaluation(state, flattenLeastCommonArray);
		return new Pair<Evaluation, SymbolicExpression>(eval, startPointer);
	}

	/**
	 * Get sequence of data between two array element references. Returns the
	 * sequence of data which is in form of an one dimensional array.
	 * 
	 * @author Ziqing Luo
	 * @param state
	 *            The current state
	 * @param process
	 *            The information of the process
	 * @param startPtr
	 *            The pointer to the start position
	 * @param endPtr
	 *            The pointer to the end position
	 * @param arrayElementsSizes
	 *            same as the same argument in {@link #setDataBetween(State,
	 *            String, SymbolicExpression, SymbolicExpression,
	 *            SymbolicExpression, Map<Integer, NumericExpression>,
	 *            CIVLSource)}
	 * @param source
	 *            The CIVL source of start pointer.
	 * @return a sequence of data which is in form of an one dimensional array.
	 * @throws UnsatisfiablePathConditionException
	 */
	public SymbolicExpression getDataBetween(State state, String process,
			SymbolicExpression startPtr, SymbolicExpression endPtr,
			ArrayList<NumericExpression> arrayElementsSizes, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression startPointer, endPointer;
		SymbolicExpression oldLeastCommonArray = null;
		SymbolicExpression flattenedLeastComArray;
		NumericExpression startPos = zero;
		NumericExpression endPos = zero;
		NumericExpression dataLength;
		Map<Integer, NumericExpression> startIndexes;
		Map<Integer, NumericExpression> endIndexes;
		boolean sidMatch, vidMatch;
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		int dim = 0;
		ResultType resultType;

		// Checking if both of the pointers are pointing to the same obejct
		sidMatch = (symbolicUtil.getDyscopeId(source, startPtr) == symbolicUtil
				.getDyscopeId(source, endPtr));
		vidMatch = (symbolicUtil.getVariableId(source, startPtr) == symbolicUtil
				.getVariableId(source, endPtr));
		if (!(sidMatch && vidMatch))
			throw new CIVLInternalException("Object unmatch exception\n",
					source);
		// Cast pointers to the form of an array element reference
		startPointer = symbolicAnalyzer.castToArrayElementReference(state,
				startPtr, source);
		endPointer = endPtr;
		startIndexes = symbolicAnalyzer.arrayIndexesByPointer(state, source,
				startPointer, false);
		endIndexes = symbolicAnalyzer.arrayIndexesByPointer(state, source,
				endPointer, false);
		// If sizes of the two sets are not equal which means endPointer is
		// still pointing to a array type component. Then we need cast it.
		if (startIndexes.size() != endIndexes.size()) {
			endPointer = symbolicAnalyzer.castToArrayElementReference(state,
					endPtr, source);
			endIndexes = symbolicAnalyzer.arrayIndexesByPointer(state, source,
					endPointer, false);
		}
		while (!startPointer.equals(endPointer)) {
			startPos = universe.add(
					startPos,
					universe.multiply(startIndexes.get(dim),
							arrayElementsSizes.get(dim)));
			endPos = universe.add(
					endPos,
					universe.multiply(endIndexes.get(dim),
							arrayElementsSizes.get(dim)));
			dim++;
			startPointer = symbolicUtil.parentPointer(source, startPointer);
			endPointer = symbolicUtil.parentPointer(source, endPointer);
		}
		dataLength = universe.add(universe.subtract(endPos, startPos), one);
		assert (reasoner.isValid(universe.lessThanEquals(zero, dataLength)));
		oldLeastCommonArray = evaluator.dereference(source, state, process,
				startPointer, false).value;
		if (!(oldLeastCommonArray.type() instanceof SymbolicArrayType)) {
			BooleanExpression claim = universe.equals(dataLength, one);

			resultType = reasoner.valid(claim).getResultType();
			if (!resultType.equals(ResultType.YES)) {
				state = errorLogger.logError(
						source,
						state,
						process,
						symbolicAnalyzer.stateToString(state),
						claim,
						resultType,
						ErrorKind.OUT_OF_BOUNDS,
						"Array index out of bound when reading from object pointed by "
								+ symbolicAnalyzer.symbolicExpressionToString(
										source, state, startPtr) + ".\n"
								+ "Data size: 1\n" + "Expected data size: "
								+ dataLength + "\n");
			}
			return universe.array(oldLeastCommonArray.type(),
					Arrays.asList(oldLeastCommonArray));
		}
		flattenedLeastComArray = arrayFlatten(state, process,
				oldLeastCommonArray, source);
		try {
			// TODO: throw null pointer exception is bug in get sub array
			flattenedLeastComArray = symbolicAnalyzer.getSubArray(
					flattenedLeastComArray, startPos,
					universe.add(endPos, one), state, process, source);
		} catch (java.lang.NullPointerException e) {
			throw new CIVLInternalException("Get subarray from index:"
					+ startPos
					+ " to "
					+ endPos
					+ " on array:"
					+ symbolicAnalyzer.symbolicExpressionToString(source,
							state, flattenedLeastComArray), source);
		}
		return flattenedLeastComArray;
	}

	/* ******************* Output Args Assignment Helpers ******************** */
	/**
	 * Recursively flatten the given array. Only can be used on arrays have
	 * concrete lengths.
	 */
	private List<SymbolicExpression> arrayFlattenWorker(State state,
			SymbolicExpression array, CIVLSource civlsource) {
		BooleanExpression pathCondition = state.getPathCondition();
		List<SymbolicExpression> flattenElementList = new LinkedList<>();
		Reasoner reasoner = universe.reasoner(pathCondition);

		if (array.isNull() || array == null)
			throw new CIVLInternalException("parameter array is null.",
					civlsource);

		if (array.type() instanceof SymbolicArrayType) {
			BooleanExpression claim;
			NumericExpression i = universe.zeroInt();
			NumericExpression length = universe.length(array);

			claim = universe.lessThan(i, length);
			if (((SymbolicArrayType) array.type()).elementType() instanceof SymbolicArrayType) {
				while (reasoner.isValid(claim)) {
					SymbolicExpression element = universe.arrayRead(array, i);

					flattenElementList.addAll(arrayFlattenWorker(state,
							element, civlsource));
					// update
					i = universe.add(i, one);
					claim = universe.lessThan(i, length);
				}
			} else {
				while (reasoner.isValid(claim)) {
					SymbolicExpression element = universe.arrayRead(array, i);

					flattenElementList.add(element);
					// update
					i = universe.add(i, one);
					claim = universe.lessThan(i, length);
				}
			}
		} else {
			flattenElementList.add(array);
		}
		return flattenElementList;
	}

	/**
	 * Helper function for
	 * {@link #arrayFlatten(State, String, SymbolicExpression, CIVLSource)}.
	 * Used for dealing with arrays have non-concrete lengths.
	 */
	private SymbolicExpression arrayLambdaFlatten(State state,
			SymbolicExpression array,
			ArrayList<NumericExpression> arrayElementsSizes,
			CIVLSource civlsource) {
		// Temporary array object during processing
		SymbolicExpression tempArray = array;
		NumericSymbolicConstant index = null;
		SymbolicType elementType = null;
		SymbolicExpression arrayEleFunc = null;
		SymbolicExpression lambdaFunc;
		SymbolicExpression newArray = null;
		SymbolicCompleteArrayType newArrayType;
		int dim;
		NumericExpression capacity = one;
		NumericExpression tempIndex;
		NumericExpression newExtent;

		index = (NumericSymbolicConstant) universe.symbolicConstant(
				universe.stringObject("i"), universe.integerType());
		// From outer to inner. later from inner to outer
		dim = arrayElementsSizes.size();
		tempIndex = index;
		newExtent = one;
		for (int i = 0; i < dim; i++) {
			NumericExpression newIndex; // new index is remainder

			capacity = arrayElementsSizes.get(dim - 1 - i);
			newIndex = universe.divide(tempIndex, capacity);
			newExtent = universe
					.multiply(newExtent, universe.length(tempArray));
			tempArray = universe.arrayRead(tempArray, newIndex);
			tempIndex = universe.modulo(tempIndex, capacity);
		}
		elementType = tempArray.type();
		arrayEleFunc = universe.canonic(tempArray);
		lambdaFunc = universe.lambda(index, arrayEleFunc);
		newArrayType = universe.arrayType(elementType, newExtent);
		newArray = universe.arrayLambda(newArrayType, lambdaFunc);
		assert (newArray != null);
		return newArray;
	}

	/**
	 * Helper function for
	 * {@link #arrayFlatten(State , String, SymbolicExpression , CIVLSource)}.
	 * Returns true if and only if there is at least one array (in nested arrays
	 * ) has non-concrete length.
	 */
	private boolean hasNonConcreteExtent(Reasoner reasoner,
			SymbolicExpression array) {
		NumericExpression extent;
		SymbolicExpression element = array;
		SymbolicType type = array.type();

		while (type instanceof SymbolicArrayType) {
			extent = universe.length(element);
			if (reasoner.extractNumber(extent) == null)
				return true;
			element = universe.arrayRead(element, zero);
			type = element.type();
		}
		return false;
	}

	/**
	 * Computes the size of the given array. Here size means the number of
	 * non-array elements that the given array can hold.
	 * 
	 * @param array
	 *            Target array
	 * @param source
	 *            CIVL source of the array or the pointer to the array
	 * @return the size of the array
	 */
	private NumericExpression arraySize(SymbolicExpression array,
			CIVLSource source) {
		ArrayList<NumericExpression> dimExtents;
		NumericExpression size = one;
		int dim = 0;

		dimExtents = symbolicUtil.arrayExtents(source, array);
		dim = dimExtents.size();
		for (int i = 0; i < dim; i++)
			size = universe.multiply(size, dimExtents.get(i));
		return size;
	}
}
