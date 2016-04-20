package edu.udel.cis.vsl.civl.library.common;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
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
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.ArrayElementReference;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType.SymbolicTypeKind;

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
			SymbolicAnalyzer symbolicAnalyzer, CIVLConfiguration civlConfig,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, evaluator.universe(), symbolicUtil, symbolicAnalyzer,
				civlConfig, libEvaluatorLoader, modelFactory);
		this.evaluator = evaluator;
		this.stateFactory = evaluator.stateFactory();
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
	 * Pre-conditions:
	 * <ol>
	 * <li>"pointer" is a valid pointer</li>
	 * <li>"count" greater than zero</li>
	 * <li>"dataArray" is an one dimensional array</li>
	 * <li>"pointer" must points to a compatible type with the "dataArray"</li>
	 * </ol>
	 * post_condition:
	 * <ol>
	 * <li>Return a sequence of data with length "count" from the pointed object
	 * starting from the pointed position</li>
	 * </ol>
	 * Setting a sequence of data starting from a pointer
	 * 
	 * @param state
	 *            The current state
	 * @param process
	 *            The information of the process
	 * @param pointer
	 *            The pointer to the start position
	 * @param count
	 *            The number of cells in the array of data
	 * @param dataArray
	 *            The sequence of data is going to be set
	 * @param checkOutput
	 *            Flag for check output variable
	 * @param source
	 *            CIVL source of the statement
	 * @return A pair of evaluation and pointer.The data in form of an array
	 *         which can be assigned to the returned pointer.
	 * @throws UnsatisfiablePathConditionException
	 */
	public Pair<Evaluation, SymbolicExpression> setDataFrom(State state,
			String process, Expression ptrExpr, SymbolicExpression pointer,
			NumericExpression count, SymbolicExpression dataArray,
			boolean checkOutput, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		NumericExpression[] arraySlicesSizes;
		NumericExpression startPos;
		NumericExpression dataSeqLength = universe.length(dataArray);
		SymbolicExpression startPtr, endPtr;
		Evaluation eval;
		Pair<Evaluation, NumericExpression[]> eval_and_slices;
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		ReferenceExpression symref;
		BooleanExpression claim;
		ResultType resultType;
		int dim;

		// If data length > count, report an error:
		claim = universe.lessThan(dataSeqLength, count);
		resultType = reasoner.valid(claim).getResultType();
		if (resultType.equals(ResultType.YES)) {
			state = reportOutOfBoundError(state, process, claim, resultType,
					pointer, dataSeqLength, count, source);
			return new Pair<>(new Evaluation(state, dataArray), pointer);
		}
		// If count is one:
		if (reasoner.isValid(universe.equals(count, one))) {
			SymbolicExpression data = universe.arrayRead(dataArray, zero);

			return new Pair<>(new Evaluation(state, data), pointer);
		}
		// Else, count greater than one:
		startPtr = pointer;
		eval_and_slices = evaluator.evaluatePointerAdd(state, process,
				startPtr, count, checkOutput, source);
		eval = eval_and_slices.left;
		endPtr = eval.value;
		state = eval.state;
		arraySlicesSizes = eval_and_slices.right;
		// If the pointer addition happens to be done within one dimensional
		// space, the "arraySlicesSizes" is null and we don't really need it.
		if (arraySlicesSizes == null) {
			arraySlicesSizes = new NumericExpression[1];
			arraySlicesSizes[0] = one;
		}
		dim = arraySlicesSizes.length;
		// "startPtr" may not point to a memory base type object yet
		symref = symbolicAnalyzer.getMemBaseReference(state, startPtr, source);
		startPtr = symbolicUtil.makePointer(startPtr, symref);
		startPos = zero;
		if (symref.isArrayElementReference()) {
			NumericExpression[] startIndices = symbolicUtil
					.stripIndicesFromReference((ArrayElementReference) symref);
			int numIndices = startIndices.length;

			for (int i = 1; !startPtr.equals(endPtr); i++) {
				startPtr = symbolicUtil.parentPointer(source, startPtr);
				endPtr = symbolicUtil.parentPointer((CIVLSource) null, endPtr);
				startPos = universe.add(startPos, universe
						.multiply(startIndices[numIndices - i],
								arraySlicesSizes[dim - i]));
			}
		}
		// here "startPtr" is already updated as the pointer to the common sub
		// array.
		eval = evaluator.dereference(source, state, process, ptrExpr, startPtr,
				false);
		state = eval.state;
		if (eval.value.type().typeKind().equals(SymbolicTypeKind.ARRAY)) {
			eval = this.setDataBetween(state, process, eval.value,
					arraySlicesSizes, startPos, count, pointer, dataArray,
					source);
			return new Pair<>(eval, startPtr);
		} else {
			state = reportOutOfBoundError(state, process, null, null, startPtr,
					one, count, source);
			return new Pair<>(new Evaluation(state, dataArray), pointer);
		}
	}

	/**
	 * Pre-condition:
	 * <ol>
	 * <li>"pointer" is valid</li>
	 * <li>"count" > 0</li>
	 * </ol>
	 * post_condition:
	 * <ol>
	 * <li>Return a sequence of data with length "count" from the pointed object
	 * starting from the pointed position</li>
	 * </ol>
	 * Get a sequence of data starting from a pointer.
	 * 
	 * @param state
	 *            The current state
	 * @param process
	 *            The information of the process
	 * @param pointer
	 *            The pointer to the start position of a sequence of data
	 * @param count
	 *            The number of cells in the array of data
	 * @param checkOutput
	 *            Flag for check output variable
	 * @param source
	 *            CIVL source of the statement
	 * @return Evaluation contains the sequence of data which is in form of a
	 *         one dimensional array.
	 * @throws UnsatisfiablePathConditionException
	 */
	public Evaluation getDataFrom(State state, String process,
			Expression pointerExpr, SymbolicExpression pointer,
			NumericExpression count, boolean checkOutput, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		NumericExpression[] arraySlicesSizes;
		NumericExpression startPos;
		SymbolicExpression startPtr, endPtr;
		SymbolicExpression commonArray;
		ReferenceExpression symref;
		Evaluation eval;
		int dim;
		Pair<Evaluation, NumericExpression[]> pointer_and_slices;
		Reasoner reasoner = universe.reasoner(state.getPathCondition());

		// If "count" == 1:
		if (reasoner.isValid(universe.equals(count, one))) {
			eval = evaluator.dereference(source, state, process, pointerExpr,
					pointer, true);
			eval.value = universe.array(eval.value.type(),
					Arrays.asList(eval.value));
			eval.value = this.arrayFlatten(state, process, eval.value, source);
			return eval;
		}
		// Else "count" > 1 :
		startPtr = pointer;
		pointer_and_slices = evaluator.evaluatePointerAdd(state, process,
				startPtr, count, false, source);
		arraySlicesSizes = pointer_and_slices.right;
		eval = pointer_and_slices.left;
		endPtr = eval.value;
		// If the pointer addition happens to be done within one dimensional
		// space, the "arraySlicesSizes" is null and we don't really need it.
		if (arraySlicesSizes == null) {
			arraySlicesSizes = new NumericExpression[1];
			arraySlicesSizes[0] = one;
		}
		// startPtr may not be the memory base type reference form yet
		symref = symbolicAnalyzer.getMemBaseReference(state, startPtr, source);
		startPtr = symbolicUtil.makePointer(startPtr, symref);
		startPos = zero;
		if (symref.isArrayElementReference()) {
			NumericExpression[] startPtrIndices = symbolicUtil
					.stripIndicesFromReference((ArrayElementReference) symref);
			int numIndices = startPtrIndices.length;

			dim = arraySlicesSizes.length;
			for (int i = 1; !startPtr.equals(endPtr); i++) {
				startPtr = symbolicUtil.parentPointer(source, startPtr);
				endPtr = symbolicUtil.parentPointer((CIVLSource) null, endPtr);
				startPos = universe.add(startPos, universe.multiply(
						startPtrIndices[numIndices - i], arraySlicesSizes[dim
								- i]));
			}
		}
		eval = evaluator.dereference(source, state, process, pointerExpr,
				startPtr, true);
		state = eval.state;
		commonArray = eval.value;
		if (commonArray.type().typeKind().equals(SymbolicTypeKind.ARRAY))
			eval.value = getDataBetween(state, process, startPos, count,
					commonArray, arraySlicesSizes, source);
		else
			state = reportOutOfBoundError(state, process, null, null, startPtr,
					one, count, source);
		return eval;
	}

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
			SymbolicExpression oldArray,
			SymbolicCompleteArrayType typeTemplate, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		BooleanExpression claim;
		NumericExpression[] coordinatesSizes, arraySlicesSizes;
		// temporary arrays store dimensional slices
		SymbolicExpression[] arraySlices;
		SymbolicExpression flattenOldArray;
		ResultType resultType;
		IntegerNumber flattenLength;
		IntegerNumber dimensionalSpace;
		SymbolicType elementType;
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		int dim, numElements;

		assert (typeTemplate.typeKind().equals(SymbolicTypeKind.ARRAY));
		assert typeTemplate.isComplete() : "arrayCasting internal exception";
		if (oldArray.type().equals(typeTemplate))
			return oldArray;
		flattenOldArray = arrayFlatten(state, process, oldArray, source);
		flattenLength = (IntegerNumber) reasoner.extractNumber(universe
				.length(flattenOldArray));
		if (flattenLength == null)
			throw new CIVLUnimplementedFeatureException(
					"Transform arrays with non-concrete sizes");
		arraySlices = new SymbolicExpression[flattenLength.intValue()];
		coordinatesSizes = symbolicUtil.arrayCoordinateSizes(typeTemplate);
		arraySlicesSizes = symbolicUtil.arraySlicesSizes(coordinatesSizes);
		elementType = ((SymbolicArrayType) flattenOldArray.type())
				.elementType();
		// check if the flatten array is compatible with the given array type
		claim = universe.equals(universe.length(flattenOldArray),
				universe.multiply(arraySlicesSizes[0], coordinatesSizes[0]));
		resultType = reasoner.valid(claim).getResultType();
		if (!resultType.equals(ResultType.YES))
			throw new CIVLInternalException(
					"Casting an array between incompatiable types", source);
		dim = coordinatesSizes.length;
		// Extracting sub-arrays out of SYMBOLIC flatten array
		dimensionalSpace = (IntegerNumber) reasoner
				.extractNumber(coordinatesSizes[dim - 1]);
		if (dimensionalSpace == null)
			throw new CIVLUnimplementedFeatureException(
					"Transform arrays with non-concrete sizes");
		numElements = flattenLength.intValue();
		for (int j = 0, i = 0; j < flattenLength.intValue(); j += dimensionalSpace
				.intValue()) {
			arraySlices[i++] = symbolicAnalyzer.getSubArray(flattenOldArray,
					universe.integer(j), universe.add(universe.integer(j),
							coordinatesSizes[dim - 1]), state, process, source);
		}
		numElements /= dimensionalSpace.intValue();
		elementType = universe
				.arrayType(elementType, coordinatesSizes[dim - 1]);
		// Keep compressing sub-arrays
		for (int i = dim - 1; --i >= 0;) {
			SymbolicExpression[] subArray;

			dimensionalSpace = (IntegerNumber) reasoner
					.extractNumber(coordinatesSizes[i]);
			if (dimensionalSpace == null)
				throw new CIVLUnimplementedFeatureException(
						"Transform arrays with non-concrete sizes");
			numElements /= dimensionalSpace.intValue();
			for (int j = 0; j < numElements; j++) {
				int offset = j * dimensionalSpace.intValue();

				subArray = Arrays.copyOfRange(arraySlices, offset, offset
						+ dimensionalSpace.intValue());
				arraySlices[j] = universe.array(elementType,
						Arrays.asList(subArray));
			}
			elementType = universe.arrayType(elementType, coordinatesSizes[i]);
		}
		return arraySlices[0];
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
		NumericExpression[] arrayElementsSizes;
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
			if (array.type().typeKind().equals(SymbolicTypeKind.ARRAY))
				arrayElementsSizes = symbolicUtil.arraySlicesSizes(symbolicUtil
						.arrayCoordinateSizes((SymbolicCompleteArrayType) array
								.type()));
			else {
				arrayElementsSizes = new NumericExpression[1];
				arrayElementsSizes[0] = one;
			}
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

	/* ************* Private helper functions ************ */
	/**
	 * Pre-condition:
	 * <ol>
	 * <li>"pointer" points to the start position</li>
	 * <li>"count" > 0</li>
	 * <li>"count" >= length(dataSequence)</li>
	 * <li>"array" has {@link SymbolicCompleteArrayType}</li>
	 * <li>"dataSequence" is an one dimensional array</li>
	 * </ol>
	 * Post-condition:
	 * <ol>
	 * <li>left side of the pair: Return the new value of the pointed object
	 * after assigning the given data sequence from pointed position</li>
	 * <li>right side of the pair: Return the pointer which can be assigned with
	 * the new value</li>
	 * </ol>
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
	 * @param dataSequence
	 *            The sequence of data which is going to be set
	 * @param arraySlicesSizes
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
	private Evaluation setDataBetween(State state, String process,
			SymbolicExpression array, NumericExpression[] arraySlicesSizes,
			NumericExpression startPos, NumericExpression count,
			SymbolicExpression pointer, SymbolicExpression dataSequence,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression flattenArray;
		NumericExpression dataSize;
		NumericExpression i, j;
		BooleanExpression claim;
		Reasoner reasoner = universe.reasoner(state.getPathCondition());

		dataSize = universe.length(dataSequence);
		// Direct assignment conditions:
		// 1. start position is zero.
		// 2. Interval between pointers equals to data size.
		// 3. The least common array capacity equals to data size.
		if (reasoner.isValid(universe.equals(startPos, zero))) {
			NumericExpression arraySize = universe.length(array);

			claim = universe.and(universe.equals(dataSize, count),
					universe.equals(dataSize, arraySize));
			if (reasoner.isValid(claim)) {
				if (array.type().typeKind().equals(SymbolicTypeKind.ARRAY))
					dataSequence = arrayCasting(state, process, dataSequence,
							(SymbolicCompleteArrayType) array.type(), source);
				return new Evaluation(state, dataSequence);
			}
		}// TODO: what if the length of dataSize is non-concrete and cannot be
			// decided by reasoner?
		flattenArray = arrayFlatten(state, process, array, source);
		i = startPos;
		j = zero;
		claim = universe.lessThan(j, dataSize);
		while (reasoner.isValid(claim)) {
			SymbolicExpression elementInDataArray = null;

			elementInDataArray = universe.arrayRead(dataSequence, j);
			flattenArray = universe.arrayWrite(flattenArray, i,
					elementInDataArray);
			i = universe.add(i, one);
			j = universe.add(j, one);
			claim = universe.lessThan(j, dataSize);
		}
		flattenArray = arrayCasting(state, process, flattenArray,
				(SymbolicCompleteArrayType) array.type(), source);
		return new Evaluation(state, flattenArray);
	}

	/**
	 * pre-condition:
	 * <ol>
	 * <li>endPos - startPos > 0</li>
	 * <li>array has {@link SymbolicCompleteArrayType}</li>
	 * <li>arraySlicesSize[0] >= endPos - startPos</li>
	 * </ol>
	 * post_condition:
	 * <ol>
	 * <li>Return a sequence of data with length "count" from the pointed object
	 * starting from the pointed position</li>
	 * </ol>
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
	private SymbolicExpression getDataBetween(State state, String process,
			NumericExpression startPos, NumericExpression count,
			SymbolicExpression array, NumericExpression[] arraySlicesSizes,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression flattenArray;

		// TODO: getSubArray not support non-concrete length
		flattenArray = arrayFlatten(state, process, array, source);
		return symbolicAnalyzer.getSubArray(flattenArray, startPos,
				universe.add(startPos, count), state, process, source);
	}

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
			SymbolicExpression array, NumericExpression[] arrayElementsSizes,
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
		dim = arrayElementsSizes.length;
		tempIndex = index;
		newExtent = one;
		for (int i = 0; i < dim; i++) {
			NumericExpression newIndex; // new index is remainder

			capacity = arrayElementsSizes[i];
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
	 * Helper function of report an out of bound error.
	 * 
	 * @param state
	 *            The current state
	 * @param process
	 *            The string identifier of the process
	 * @param claim
	 *            The {@link BooleanExpression} of the predicate (optional, can
	 *            be null)
	 * @param resultType
	 *            The {@link ResultType} of reasoning the predicate (optional,
	 *            can be null)
	 * @param pointer
	 *            The pointer to the array
	 * @param arrayLength
	 *            The length of the array
	 * @param offset
	 *            The offset of the element from the position pointed by pointer
	 * @param source
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State reportOutOfBoundError(State state, String process,
			BooleanExpression claim, ResultType resultType,
			SymbolicExpression pointer, NumericExpression arrayLength,
			NumericExpression offset, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		String message = "Out of bound error may happen when access on an array element.\n"
				+ "Pointer:"
				+ symbolicAnalyzer.symbolicExpressionToString(source, state,
						pointer)
				+ "\n"
				+ "Offset:"
				+ symbolicAnalyzer.symbolicExpressionToString(source, state,
						offset)
				+ "\n"
				+ "Array length:"
				+ symbolicAnalyzer.symbolicExpressionToString(source, state,
						arrayLength);

		if (claim == null || resultType == null) {
			errorLogger.logSimpleError(source, state, process,
					symbolicAnalyzer.stateToString(state),
					ErrorKind.OUT_OF_BOUNDS, message);
			return state;
		}
		return errorLogger.logError(source, state, process,
				symbolicAnalyzer.stateToString(state), claim, resultType,
				ErrorKind.OUT_OF_BOUNDS, message);

	}
}
