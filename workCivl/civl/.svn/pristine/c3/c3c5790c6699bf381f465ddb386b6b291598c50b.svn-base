package edu.udel.cis.vsl.civl.dynamic.common;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.civl.util.IF.Singleton;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.ArrayElementReference;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NTReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.TupleComponentReference;
import edu.udel.cis.vsl.sarl.IF.expr.UnionMemberReference;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType.SymbolicTypeKind;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicUnionType;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicSequence;

public class CommonSymbolicUtility implements SymbolicUtility {

	/* *************************** Instance Fields ************************* */

	/**
	 * Symbolic universe for operations on symbolic expressions.
	 */
	private SymbolicUniverse universe;

	/**
	 * The model factory of the CIVL model.
	 */
	private ModelFactory modelFactory;

	/**
	 * Integer object 0.
	 */
	private IntObject zeroObj;

	/**
	 * Integer object 1.
	 */
	private IntObject oneObj;

	/**
	 * Integer object 2.
	 */
	private IntObject twoObj;

	/**
	 * Integer 0.
	 */
	private NumericExpression zero;

	/**
	 * Integer 1.
	 */
	private NumericExpression one;

	/**
	 * The uninterpreted function sizeof.
	 */
	private SymbolicExpression sizeofFunction;

	/**
	 * Symbolic dynamic type.
	 */
	private SymbolicTupleType dynamicType;

	/**
	 * Map from symbolic type to a canonic symbolic expression of that type.
	 */
	private Map<SymbolicType, SymbolicExpression> typeExpressionMap = new HashMap<>();

	/**
	 * The map of symbolic types and their ID's.
	 */
	private Map<SymbolicType, NumericExpression> sizeofDynamicMap = new HashMap<>();

	/**
	 * The symbolic expression of boolean false.
	 */
	private BooleanExpression falseValue;

	/**
	 * The symbolic expression of boolean true.
	 */
	private BooleanExpression trueValue;

	/**
	 * The symbolic expression of NULL pointer.
	 */
	private SymbolicExpression nullPointer;

	/**
	 * The symbolic expression of undefined pointer, i.e., a pointer that has
	 * been deallocated.
	 */
	private SymbolicExpression undefinedPointer;

	/**
	 * The heap analyzer for heap related semantics.
	 */
	private HeapAnalyzer heapAnalyzer;

	/**
	 * The symbolic pointer type.
	 */
	private SymbolicTupleType pointerType;

	/* ***************************** Constructor *************************** */

	public CommonSymbolicUtility(SymbolicUniverse universe,
			ModelFactory modelFactory) {
		SymbolicType dynamicToIntType;

		this.universe = universe;
		this.modelFactory = modelFactory;
		this.heapAnalyzer = new HeapAnalyzer(universe, this);
		dynamicType = modelFactory.dynamicSymbolicType();
		dynamicToIntType = universe.functionType(new Singleton<SymbolicType>(
				dynamicType), universe.integerType());
		sizeofFunction = universe.symbolicConstant(
				universe.stringObject("SIZEOF"), dynamicToIntType);
		sizeofFunction = universe.canonic(sizeofFunction);
		this.zeroObj = (IntObject) universe.canonic(universe.intObject(0));
		this.oneObj = (IntObject) universe.canonic(universe.intObject(1));
		this.twoObj = (IntObject) universe.canonic(universe.intObject(2));
		zero = (NumericExpression) universe.canonic(universe.integer(0));
		one = (NumericExpression) universe.canonic(universe.integer(1));
		this.falseValue = (BooleanExpression) universe.canonic(universe
				.falseExpression());
		this.trueValue = (BooleanExpression) universe.canonic(universe
				.trueExpression());
		this.pointerType = this.modelFactory.pointerSymbolicType();
		this.nullPointer = universe.canonic(this.makePointer(-1, -1,
				universe.nullReference()));
		this.undefinedPointer = universe.canonic(this.makePointer(-2, -2,
				universe.nullReference()));
	}

	/* ********************* Methods from SymbolicUtility ******************* */

	/**
	 * Given a symbolic expression of type array of char, returns a string
	 * representation. If it is a concrete array of char consisting of concrete
	 * characters, this will be the obvious string. Otherwise the result is
	 * something readable but unspecified.
	 * 
	 * @throws UnsatisfiablePathConditionException
	 */
	@Override
	public StringBuffer charArrayToString(CIVLSource source,
			SymbolicSequence<?> charArray, int startIndex, boolean forPrint) {
		StringBuffer result = new StringBuffer();
		int numChars = charArray.size();

		// ignoring the '\0' at the end of the string.
		for (int j = startIndex; j < numChars; j++) {
			SymbolicExpression charExpr = charArray.get(j);
			Character theChar = universe.extractCharacter(charExpr);

			if (theChar == null)
				throw new CIVLUnimplementedFeatureException(
						"non-concrete character in string at position " + j,
						source);
			if (theChar != '\0') {
				if (forPrint) {
					String theCharToString;
					switch (theChar) {
					case '\u000C':
						theCharToString = "\\f";
						break;
					case '\u0007':
						theCharToString = "\\a";
						break;
					case '\b':
						theCharToString = "\\b";
						break;
					case '\n':
						theCharToString = "\\n";
						break;
					case '\t':
						theCharToString = "\\t";
						break;
					case '\r':
						theCharToString = "\\r";
						break;
					default:
						theCharToString = theChar.toString();
					}
					result.append(theCharToString);
				} else {
					result.append(theChar);
				}
			}
		}
		return result;
	}

	/**
	 * A pointer can be only concrete for the current implementation of CIVL,
	 * because the only way to make one is through <code>$malloc</code> or
	 * <code>&</code>.
	 */
	@Override
	public BooleanExpression contains(SymbolicExpression pointer1,
			SymbolicExpression pointer2) {
		// TODO checks null pointer
		ReferenceExpression ref1 = (ReferenceExpression) universe.tupleRead(
				pointer1, twoObj);
		ReferenceExpression ref2 = (ReferenceExpression) universe.tupleRead(
				pointer2, twoObj);
		SymbolicExpression scope1 = universe.tupleRead(pointer1, zeroObj);
		SymbolicExpression scope2 = universe.tupleRead(pointer2, zeroObj);
		SymbolicExpression vid1 = universe.tupleRead(pointer1, oneObj);
		SymbolicExpression vid2 = universe.tupleRead(pointer2, oneObj);
		List<ReferenceExpression> refComps1 = new ArrayList<>();
		List<ReferenceExpression> refComps2 = new ArrayList<>();
		int numRefs1, numRefs2, offset;
		BooleanExpression result = this.trueValue;

		if (ref1.isIdentityReference() && ref2.isIdentityReference()) {
			return (BooleanExpression) universe.canonic(universe.equals(ref1,
					ref2));
		}
		if (ref2.isIdentityReference() // second contains first
				|| universe.equals(scope1, scope2).isFalse() // different scope
																// id
				|| universe.equals(vid1, vid2).isFalse()) // different vid
			return this.falseValue;
		if (ref1.isIdentityReference() && !ref2.isIdentityReference())
			return this.trueValue;
		refComps1 = referenceComponents(ref1);
		refComps2 = referenceComponents(ref2);
		numRefs1 = refComps1.size();
		numRefs2 = refComps2.size();
		if (numRefs1 > numRefs2)
			return this.falseValue;
		offset = numRefs2 - numRefs1;
		for (int i = offset; i < numRefs1; i++) {
			result = universe.and(result, universe.equals(refComps1.get(i),
					refComps2.get(i + offset)));
		}
		return result;
	}

	@Override
	public int extractInt(CIVLSource source, NumericExpression expression) {
		IntegerNumber result = (IntegerNumber) universe
				.extractNumber(expression);

		if (result == null)
			throw new CIVLInternalException(
					"Unable to extract concrete int from " + expression, source);
		return result.intValue();
	}

	@Override
	public int extractIntField(CIVLSource source, SymbolicExpression tuple,
			IntObject fieldIndex) {
		NumericExpression field = (NumericExpression) universe.tupleRead(tuple,
				fieldIndex);

		return this.extractInt(source, field);
	}

	@Override
	public SymbolicExpression expressionOfType(SymbolicType type) {
		SymbolicExpression result;

		type = (SymbolicType) universe.canonic(type);
		result = typeExpressionMap.get(type);
		if (result == null) {
			SymbolicExpression id = universe.integer(type.id());

			result = universe.canonic(universe.tuple(dynamicType,
					new Singleton<SymbolicExpression>(id)));
			typeExpressionMap.put(type, result);
		}
		return result;
	}

	@Override
	public int getArrayIndex(CIVLSource source, SymbolicExpression pointer) {
		int int_arrayIndex;

		if (pointer.type() instanceof SymbolicArrayType) {
			int_arrayIndex = 0;
		} else {// TODO what if pointer is pointing to the heap?
			ArrayElementReference arrayRef = (ArrayElementReference) getSymRef(pointer);
			NumericExpression arrayIndex = arrayRef.getIndex();

			int_arrayIndex = extractInt(source, arrayIndex);
		}
		return int_arrayIndex;
	}

	@Override
	public int getDyscopeId(CIVLSource source, SymbolicExpression pointer) {
		return modelFactory.getScopeId(source,
				universe.tupleRead(pointer, zeroObj));
	}

	@Override
	public NumericExpression getRangeMax(SymbolicExpression range) {
		return (NumericExpression) universe.tupleRead(range, oneObj);
	}

	@Override
	public SymbolicExpression getLowOfDomainAt(SymbolicExpression domain,
			int index) {
		SymbolicExpression range = universe.tupleRead(domain,
				universe.intObject(index));

		return universe.tupleRead(range, zeroObj);
	}

	@Override
	public NumericExpression getRegRangeMin(SymbolicExpression range) {
		return (NumericExpression) universe.tupleRead(range, zeroObj);
	}

	@Override
	public NumericExpression getRangeSize(SymbolicExpression range) {
		NumericExpression low = (NumericExpression) universe.tupleRead(range,
				this.zeroObj);
		NumericExpression high = (NumericExpression) universe.tupleRead(range,
				oneObj);
		NumericExpression step = (NumericExpression) universe.tupleRead(range,
				this.twoObj);
		NumericExpression size = universe.subtract(high, low);
		NumericExpression remainder = universe.modulo(size, step);

		size = universe.subtract(size, remainder);
		size = universe.divide(size, step);
		size = universe.add(size, this.one);
		return size;
	}

	@Override
	public NumericExpression getRangeStep(SymbolicExpression range) {
		return (NumericExpression) universe.tupleRead(range, twoObj);
	}

	@Override
	public ReferenceExpression getSymRef(SymbolicExpression pointer) {
		SymbolicExpression result = universe.tupleRead(pointer, twoObj);

		assert result instanceof ReferenceExpression;
		return (ReferenceExpression) result;
	}

	@Override
	public SymbolicExpression setSymRef(SymbolicExpression pointer,
			ReferenceExpression symRef) {
		return universe.tupleWrite(pointer, twoObj, symRef);
	}

	@Override
	public int getVariableId(CIVLSource source, SymbolicExpression pointer) {
		return extractIntField(source, pointer, oneObj);
	}

	@Override
	public SymbolicExpression heapMemUnit(SymbolicExpression pointer) {
		return this.heapAnalyzer.heapMemUnit(pointer);
	}

	@Override
	public SymbolicExpression initialValueOfRange(SymbolicExpression range,
			int index, int dimension) {
		SymbolicExpression low = universe.tupleRead(range, zeroObj);
		SymbolicExpression step = universe.tupleRead(range, twoObj);

		// The last range of the dimension, i.e., the first range to be
		// incremented, will have the initial value of (low - step).
		if (index == dimension - 1)
			return universe.subtract((NumericExpression) low,
					(NumericExpression) step);
		return low;
	}

	@Override
	public SymbolicConstant invalidHeapObject(SymbolicType heapObjectType) {
		return heapAnalyzer.invalidHeapObject(heapObjectType);
	}

	@Override
	public boolean isDisjointWith(SymbolicExpression pointer1,
			SymbolicExpression pointer2) {
		if (pointer1.equals(pointer2))
			return false;
		{
			SymbolicExpression scope1 = universe.tupleRead(pointer1, zeroObj), var1 = universe
					.tupleRead(pointer1, oneObj);
			SymbolicExpression scope2 = universe.tupleRead(pointer2, zeroObj), var2 = universe
					.tupleRead(pointer2, oneObj);
			ReferenceExpression ref1 = (ReferenceExpression) universe
					.tupleRead(pointer1, twoObj);
			ReferenceExpression ref2 = (ReferenceExpression) universe
					.tupleRead(pointer2, twoObj);

			if (!scope1.equals(scope2))
				return true;
			if (!var1.equals(var2))
				return true;
			if (ref1.equals(ref2))
				return false;
			return isDisjoint(ref1, ref2);
		}
	}

	@Override
	public boolean isEmptyHeap(SymbolicExpression heapValue) {
		return heapAnalyzer.isEmptyHeap(heapValue);
	}

	@Override
	public boolean isMallocPointer(CIVLSource source, SymbolicExpression pointer) {
		return heapAnalyzer.isHeapAtomicObjectPointer(source, pointer);
	}

	@Override
	public boolean isInitialized(SymbolicExpression value) {
		if (value.isNull())
			return false;
		return true;
	}

	@Override
	public BooleanExpression isInRange(SymbolicExpression value,
			SymbolicExpression domain, int index) {
		SymbolicExpression range = universe.tupleRead(domain,
				universe.intObject(index));
		SymbolicExpression high = universe.tupleRead(range, oneObj);
		SymbolicExpression step = universe.tupleRead(range, twoObj);
		BooleanExpression positiveStep = universe.lessThan(zero,
				(NumericExpression) step);
		BooleanExpression negativeStep = universe.lessThan(
				(NumericExpression) step, zero);
		BooleanExpression positiveStepResult = universe.and(positiveStep,
				universe.lessThanEquals((NumericExpression) value,
						(NumericExpression) high));
		BooleanExpression negativeStepResult = universe.and(negativeStep,
				universe.lessThanEquals((NumericExpression) high,
						(NumericExpression) value));

		if (positiveStep.isTrue())
			return universe.lessThanEquals((NumericExpression) value,
					(NumericExpression) high);
		if (negativeStep.isTrue())
			return universe.lessThanEquals((NumericExpression) high,
					(NumericExpression) value);
		return universe.or(positiveStepResult, negativeStepResult);
	}

	@Override
	public boolean isInvalidHeapObject(SymbolicExpression heapObject) {
		return heapAnalyzer.isInvalidHeapObject(heapObject);
	}

	@Override
	public boolean isNullPointer(SymbolicExpression pointer) {
		return universe.equals(this.nullPointer, pointer).isTrue();
	}

	@Override
	public boolean isHeapPointer(SymbolicExpression pointer) {
		return heapAnalyzer.isPointerToHeap(pointer);
	}

	@Override
	public boolean isUndefinedPointer(SymbolicExpression pointer) {
		if (!pointer.isNull()) {
			int dyscopeId = this.getDyscopeId(null, pointer);

			return dyscopeId == -2;
		}
		return false;
	}

	@Override
	public boolean isValidRefOf(ReferenceExpression ref,
			SymbolicExpression value) {
		return isValidRefOfValue(ref, value).right;
	}

	@Override
	public boolean isValidPointer(SymbolicExpression pointer) {
		int scopeId = this.getDyscopeId(null, pointer);

		return scopeId >= 0;
	}

	@Override
	public SymbolicExpression makePointer(int scopeId, int varId,
			ReferenceExpression symRef) {
		SymbolicExpression scopeField = modelFactory.scopeValue(scopeId);
		SymbolicExpression varField = universe.integer(varId);
		SymbolicExpression result = universe.tuple(
				this.pointerType,
				Arrays.asList(new SymbolicExpression[] { scopeField, varField,
						symRef }));

		return result;
	}

	@Override
	public SymbolicExpression extendPointer(SymbolicExpression objectPointer,
			ReferenceExpression reference) {
		ReferenceExpression objRef = (ReferenceExpression) universe.tupleRead(
				objectPointer, twoObj);
		SymbolicExpression scope = universe.tupleRead(objectPointer, zeroObj);
		SymbolicExpression vid = universe.tupleRead(objectPointer, oneObj);

		if (!objRef.isIdentityReference())
			reference = makeParentOf(objRef, reference);
		return universe
				.tuple(pointerType, Arrays.asList(scope, vid, reference));
	}

	@Override
	public SymbolicExpression newArray(BooleanExpression context,
			NumericExpression length, SymbolicExpression value) {
		Reasoner reasoner = universe.reasoner(context);
		IntegerNumber length_number = (IntegerNumber) reasoner
				.extractNumber((NumericExpression) length);

		if (length_number != null) {
			int length_int = length_number.intValue();
			List<SymbolicExpression> values = new ArrayList<>(length_int);

			for (int i = 0; i < length_int; i++)
				values.add(value);
			return universe.array(value.type(), values);
		} else {
			NumericSymbolicConstant index = (NumericSymbolicConstant) universe
					.symbolicConstant(universe.stringObject("i"),
							universe.integerType());
			SymbolicExpression arrayEleFunction = universe.lambda(index, value);
			SymbolicCompleteArrayType arrayValueType = universe.arrayType(
					value.type(), length);

			return universe.arrayLambda(arrayValueType, arrayEleFunction);
		}
	}

	@Override
	public SymbolicExpression nullPointer() {
		return this.nullPointer;
	}

	@Override
	public SymbolicExpression parentPointer(CIVLSource source,
			SymbolicExpression pointer) {
		ReferenceExpression symRef = getSymRef(pointer);

		if (symRef instanceof NTReferenceExpression)
			return setSymRef(pointer,
					((NTReferenceExpression) symRef).getParent());
		throw new CIVLInternalException("Expected non-trivial pointer: "
				+ pointer, source);
	}

	@Override
	public SymbolicExpression incrementRegularRange(SymbolicExpression value,
			SymbolicExpression range) {
		NumericExpression step = (NumericExpression) universe.tupleRead(range,
				twoObj);

		return universe.add((NumericExpression) value, step);
	}

	@Override
	public SymbolicExpression rangeOfRectangularDomainAt(
			SymbolicExpression domain, int index) {
		return universe.tupleRead(domain, universe.intObject(index));
	}

	@Override
	public ReferenceExpression referenceOfPointer(SymbolicExpression pointer) {
		ReferenceExpression ref = (ReferenceExpression) universe.tupleRead(
				pointer, twoObj);

		if (this.isHeapPointer(pointer)) {
			Pair<ReferenceExpression, Integer> refResult = heapAnalyzer
					.heapReference(ref, true);

			if (refResult.right == 3)
				return universe.identityReference();
			else
				return refResult.left;
		} else
			return ref;
	}

	@Override
	public ReferenceExpression referenceToHeapMemUnit(SymbolicExpression pointer) {
		return this.heapAnalyzer.referenceToHeapMemUnit(pointer);
	}

	@Override
	public NumericExpression sizeof(CIVLSource source, SymbolicType type) {
		NumericExpression result = sizeofDynamicMap.get(type);

		if (result == null) {

			if (type.isBoolean())
				result = modelFactory.booleanType().getSizeof();
			else if (type == modelFactory.dynamicSymbolicType())
				result = modelFactory.dynamicType().getSizeof();
			else if (type.isInteger())
				result = modelFactory.integerType().getSizeof();
			else if (type == modelFactory.processSymbolicType())
				result = modelFactory.processType().getSizeof();
			else if (type.isReal())
				result = modelFactory.realType().getSizeof();
			else if (type.typeKind() == SymbolicTypeKind.CHAR)
				result = modelFactory.charType().getSizeof();
			else if (type == modelFactory.scopeSymbolicType())
				result = modelFactory.scopeType().getSizeof();
			else if (type instanceof SymbolicCompleteArrayType) {
				SymbolicCompleteArrayType arrayType = (SymbolicCompleteArrayType) type;

				result = sizeof(source, arrayType.elementType());
				result = universe.multiply(arrayType.extent(),
						(NumericExpression) result);
			} else if (type instanceof SymbolicArrayType) {
				throw new CIVLInternalException(
						"sizeof applied to incomplete array type", source);
			} else {
				// wrap the type in an expression of type dynamicTYpe
				SymbolicExpression typeExpr = expressionOfType(type);

				result = (NumericExpression) universe.apply(sizeofFunction,
						new Singleton<SymbolicExpression>(typeExpr));
			}
			sizeofDynamicMap.put(type, result);
		}
		return result;
	}

	@Override
	public SymbolicExpression sizeofFunction() {
		return this.sizeofFunction;
	}

	@Override
	public SymbolicExpression undefinedPointer() {
		return this.undefinedPointer;
	}

	@Override
	public ReferenceExpression updateArrayElementReference(
			ArrayElementReference arrayReference,
			List<NumericExpression> newIndexes) {
		int dimension = newIndexes.size();
		ReferenceExpression rootParent = arrayReference;
		ReferenceExpression newRef;

		for (int i = 0; i < dimension; i++)
			rootParent = ((ArrayElementReference) rootParent).getParent();
		newRef = rootParent;
		for (int i = 0; i < dimension; i++) {
			newRef = universe.arrayElementReference(newRef, newIndexes.get(i));
		}
		return newRef;
	}

	/* *********************** Package-Private Methods ********************* */

	List<ReferenceExpression> ancestorsOfRef(ReferenceExpression ref) {
		if (ref.isIdentityReference())
			return new ArrayList<>();
		else {
			List<ReferenceExpression> result;

			result = ancestorsOfRef(((NTReferenceExpression) ref).getParent());
			result.add(ref);
			return result;
		}
	}

	/* *************************** Private Methods ************************* */

	/**
	 * Are the two given references disjoint?
	 * 
	 * @param ref1
	 *            The first reference expression.
	 * @param ref2
	 *            The second reference expression.
	 * @return True iff the two given references do NOT have any intersection.
	 */
	private boolean isDisjoint(ReferenceExpression ref1,
			ReferenceExpression ref2) {
		List<ReferenceExpression> ancestors1, ancestors2;
		int numAncestors1, numAncestors2, minNum;

		ancestors1 = this.ancestorsOfRef(ref1);
		ancestors2 = this.ancestorsOfRef(ref2);
		numAncestors1 = ancestors1.size();
		numAncestors2 = ancestors2.size();
		minNum = numAncestors1 <= numAncestors2 ? numAncestors1 : numAncestors2;
		for (int i = 0; i < minNum; i++) {
			ReferenceExpression ancestor1 = ancestors1.get(i), ancestor2 = ancestors2
					.get(i);

			if (!ancestor1.equals(ancestor2))
				return true;
		}
		return false;
	}

	/**
	 * Is the given reference applicable to the specified symbolic expression?
	 * 
	 * @param ref
	 *            The reference expression to be checked.
	 * @param value
	 *            The symbolic expression specified.
	 * @return True iff the given reference is applicable to the specified
	 *         symbolic expression
	 */
	private Pair<SymbolicExpression, Boolean> isValidRefOfValue(
			ReferenceExpression ref, SymbolicExpression value) {
		if (ref.isIdentityReference())
			return new Pair<>(value, true);
		else {
			ReferenceExpression parent = ((NTReferenceExpression) ref)
					.getParent();
			Pair<SymbolicExpression, Boolean> parentTest = isValidRefOfValue(
					parent, value);
			SymbolicExpression targetValue;

			if (!parentTest.right)
				return new Pair<>(value, false);
			targetValue = parentTest.left;
			if (ref.isArrayElementReference()) {
				ArrayElementReference arrayEleRef = (ArrayElementReference) ref;

				if (!(targetValue.type() instanceof SymbolicArrayType))
					return new Pair<>(targetValue, false);
				return new Pair<>(universe.arrayRead(targetValue,
						arrayEleRef.getIndex()), true);
			} else if (ref.isTupleComponentReference()) {
				TupleComponentReference tupleCompRef = (TupleComponentReference) ref;

				if (!(targetValue.type() instanceof SymbolicTupleType))
					return new Pair<>(targetValue, false);
				return new Pair<>(universe.tupleRead(targetValue,
						tupleCompRef.getIndex()), true);
			} else {
				UnionMemberReference unionMemRef = (UnionMemberReference) ref;

				if (!(targetValue.type() instanceof SymbolicUnionType))
					return new Pair<>(targetValue, false);
				return new Pair<>(universe.unionExtract(unionMemRef.getIndex(),
						targetValue), true);
			}
		}
	}

	/**
	 * Combines two references by using one as the parent of the other.
	 * 
	 * @param parent
	 *            The reference to be used as the parent.
	 * @param ref
	 *            The reference to be used as the base.
	 * @return A new reference which is the combination of the given two
	 *         references.
	 */
	private ReferenceExpression makeParentOf(ReferenceExpression parent,
			ReferenceExpression ref) {
		if (ref.isIdentityReference())
			return parent;
		else {
			ReferenceExpression myParent = makeParentOf(parent,
					((NTReferenceExpression) ref).getParent());

			if (ref.isArrayElementReference())
				return universe.arrayElementReference(myParent,
						((ArrayElementReference) ref).getIndex());
			else if (ref.isTupleComponentReference())
				return universe.tupleComponentReference(myParent,
						((TupleComponentReference) ref).getIndex());
			else
				return universe.unionMemberReference(myParent,
						((UnionMemberReference) ref).getIndex());
		}
	}

	/**
	 * Computes the components contained by a given reference expression.
	 * 
	 * @param ref
	 *            The reference expression whose components are to be computed.
	 * @return The components of the reference.
	 */
	private List<ReferenceExpression> referenceComponents(
			ReferenceExpression ref) {
		List<ReferenceExpression> components = new ArrayList<>();

		if (!ref.isIdentityReference()) {
			components.add(ref);
			components.addAll(referenceComponents(((NTReferenceExpression) ref)
					.getParent()));
		}
		return components;
	}
}
