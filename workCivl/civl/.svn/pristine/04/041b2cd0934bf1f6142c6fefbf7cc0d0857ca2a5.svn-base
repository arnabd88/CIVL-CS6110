package edu.udel.cis.vsl.civl.model.common;

import java.math.BigInteger;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLTypeFactory;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.ModelConfiguration;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.statement.MallocStatement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLBundleType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLCompleteArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLCompleteDomainType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLDomainType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLEnumType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLFunctionType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLHeapType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPointerType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPrimitiveType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPrimitiveType.PrimitiveTypeKind;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLRegularRangeType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLStructOrUnionType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.type.StructOrUnionField;
import edu.udel.cis.vsl.civl.model.common.type.CommonArrayType;
import edu.udel.cis.vsl.civl.model.common.type.CommonBundleType;
import edu.udel.cis.vsl.civl.model.common.type.CommonCompleteArrayType;
import edu.udel.cis.vsl.civl.model.common.type.CommonCompleteDomainType;
import edu.udel.cis.vsl.civl.model.common.type.CommonDomainType;
import edu.udel.cis.vsl.civl.model.common.type.CommonEnumType;
import edu.udel.cis.vsl.civl.model.common.type.CommonFunctionType;
import edu.udel.cis.vsl.civl.model.common.type.CommonHeapType;
import edu.udel.cis.vsl.civl.model.common.type.CommonPointerType;
import edu.udel.cis.vsl.civl.model.common.type.CommonPrimitiveType;
import edu.udel.cis.vsl.civl.model.common.type.CommonRegularRangeType;
import edu.udel.cis.vsl.civl.model.common.type.CommonStructOrUnionField;
import edu.udel.cis.vsl.civl.model.common.type.CommonStructOrUnionType;
import edu.udel.cis.vsl.civl.util.IF.Singleton;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicUnionType;

public class CommonCIVLTypeFactory implements CIVLTypeFactory {

	/* *********************** Package-private Fields ********************** */

	/**
	 * The unique boolean type used in the system.
	 */
	CIVLPrimitiveType booleanType;

	/**
	 * The CIVL bundle type, which is unique for a given CIVL model. A bundle
	 * type is a union type of all types referenced by a given CIVL model. A
	 * bundle type needs to be completed at the end of the construction of the
	 * model.
	 */
	CIVLBundleType bundleType;

	/**
	 * The symbolic type of the bundle type.
	 */
	SymbolicUnionType bundleSymbolicType;

	/**
	 * The unique char type used in the system.
	 */
	CIVLPrimitiveType charType;

	/**
	 * The CIVL domain type.
	 */
	CIVLDomainType domainType = null;

	/**
	 * The unique dynamic symbolic type used in the system.
	 */
	SymbolicTupleType dynamicSymbolicType;

	/**
	 * The unique dynamic type used in the system.
	 */
	CIVLPrimitiveType dynamicType;

	/**
	 * The unique symbolic function pointer type used in the system. Function
	 * pointer type need to be different from pointer type, because there is
	 * analysis particularly for pointers, like heap object reachability,
	 * reachable memory units, etc.
	 */
	SymbolicTupleType functionPointerSymbolicType;

	/**
	 * The map of handled object types and their field ID in the heap type. Each
	 * handled object type referenced in the model should have the corresponding
	 * heap field, because it will be allocated in the heap.
	 */
	Map<CIVLType, Integer> heapFieldTypeMap = new HashMap<>();

	/**
	 * The CIVL heap type, which is unique for a given CIVL model. A heap type
	 * is a struct type of all types appearing in a malloc statement, plus all
	 * handled object types used by the model. A heap type needs to be completed
	 * at the end of the construction of the model.
	 */
	CIVLHeapType heapType;

	/**
	 * The symbolic heap type
	 */
	SymbolicTupleType heapSymbolicType;

	/**
	 * The unique integer type used in the system.
	 */
	CIVLPrimitiveType integerType;

	/**
	 * The unique symbolic pointer type used in the system.
	 */
	SymbolicTupleType pointerSymbolicType;

	/**
	 * The unique symbolic process type used in the system.
	 */
	SymbolicTupleType processSymbolicType;

	/**
	 * The unique process type used in the system.
	 */
	CIVLPrimitiveType processType;

	/**
	 * The regular range type, which is (int, int, int), corresponding to (low,
	 * high, step).
	 */
	CIVLRegularRangeType rangeType = null;

	/**
	 * The unique real type used in the system.
	 */
	CIVLPrimitiveType realType;

	/**
	 * The unique scope type used in the system.
	 */
	CIVLPrimitiveType scopeType;

	/**
	 * The unique symbolic scope type used in the system.
	 */
	SymbolicTupleType scopeSymbolicType;

	/**
	 * The map of types of system libraries, e.g., $gcomm/$comm for comm, $file
	 * for stdio, $gbarrier/$barrier for concurrency, etc. A map is used so that
	 * in the future if new types are introduced by system libraries, the
	 * interface won't have to be changed.
	 */
	Map<String, CIVLType> systemTypes = new HashMap<>();

	/**
	 * The unique SARL symbolic universe used in the system.
	 */
	SymbolicUniverse universe;

	/**
	 * The unique void type used in the system.
	 */
	CIVLPrimitiveType voidType;

	/* *************************** Private Fields ************************** */

	/**
	 * The "sudo" source for objects created during translation.
	 */
	private CIVLSource systemSource = new SystemCIVLSource();

	/* **************************** Constructor **************************** */

	/**
	 * Constructs a new instance of CIVL type factory.
	 * 
	 * @param universe
	 *            The symbolic universe to be used.
	 */
	public CommonCIVLTypeFactory(SymbolicUniverse universe) {
		Iterable<SymbolicType> intTypeSingleton = new Singleton<SymbolicType>(
				universe.integerType());
		LinkedList<SymbolicType> pointerComponents = new LinkedList<>();
		LinkedList<SymbolicType> fpointerComponents = new LinkedList<>();

		this.universe = universe;
		scopeSymbolicType = (SymbolicTupleType) universe.canonic(universe
				.tupleType(universe.stringObject("scope"), intTypeSingleton));
		scopeType = primitiveType(PrimitiveTypeKind.SCOPE, scopeSymbolicType);
		processSymbolicType = (SymbolicTupleType) universe.canonic(universe
				.tupleType(universe.stringObject("process"), intTypeSingleton));
		processType = primitiveType(PrimitiveTypeKind.PROCESS,
				processSymbolicType);
		dynamicSymbolicType = (SymbolicTupleType) universe.canonic(universe
				.tupleType(universe.stringObject("dynamicType"),
						intTypeSingleton));
		dynamicType = primitiveType(PrimitiveTypeKind.DYNAMIC,
				dynamicSymbolicType);
		pointerComponents.add(scopeType.getDynamicType(universe));
		pointerComponents.add(universe.integerType());
		pointerComponents.add(universe.referenceType());
		pointerSymbolicType = (SymbolicTupleType) universe
				.canonic(universe.tupleType(universe.stringObject("pointer"),
						pointerComponents));
		fpointerComponents.add(scopeType.getDynamicType(universe));
		fpointerComponents.add(universe.integerType());
		functionPointerSymbolicType = (SymbolicTupleType) universe
				.canonic(universe.tupleType(universe.stringObject("fpointer"),
						fpointerComponents));
		this.voidType = primitiveType(PrimitiveTypeKind.VOID, null);
		this.integerType = primitiveType(PrimitiveTypeKind.INT,
				universe.integerType());
		this.booleanType = primitiveType(PrimitiveTypeKind.BOOL,
				universe.booleanType());
		this.realType = primitiveType(PrimitiveTypeKind.REAL,
				universe.realType());
		this.charType = primitiveType(PrimitiveTypeKind.CHAR,
				universe.characterType());
		this.rangeType = new CommonRegularRangeType(new CommonIdentifier(
				this.systemSource, (StringObject) universe.canonic(universe
						.stringObject("$regular_range"))), universe,
				integerType);
		this.systemTypes.put(ModelConfiguration.RANGE_TYPE, rangeType);

	}

	/* ******************* Methods from CIVLTypeFactory ******************** */

	/* *********************************************************************
	 * CIVL Types
	 * *********************************************************************
	 */

	@Override
	public void addHeapFieldObjectType(CIVLType type, int id) {
		this.heapFieldTypeMap.put(type, id);
	}

	@Override
	public int getHeapFieldId(CIVLType type) {
		if (this.heapFieldTypeMap.containsKey(type))
			return heapFieldTypeMap.get(type);
		return -1;
	}

	@Override
	public CIVLPrimitiveType booleanType() {
		return booleanType;
	}

	@Override
	public void completeHeapType(CIVLHeapType heapType,
			Collection<MallocStatement> mallocs) {
		SymbolicTupleType dynamicType = computeDynamicHeapType(mallocs);
		SymbolicExpression initialValue = computeInitialHeapValue(dynamicType);
		SymbolicExpression undefinedValue = universe.symbolicConstant(
				universe.stringObject("UNDEFINED"), dynamicType);

		undefinedValue = universe.canonic(undefinedValue);
		heapType.complete(mallocs, dynamicType, initialValue, undefinedValue);
		this.heapType = heapType;
		this.heapSymbolicType = dynamicType;
	}

	@Override
	public CIVLPrimitiveType charType() {
		return charType;
	}

	@Override
	public CIVLCompleteArrayType completeArrayType(CIVLType elementType,
			Expression extent) {
		return new CommonCompleteArrayType(elementType, extent);
	}

	@Override
	public CIVLPrimitiveType dynamicType() {
		return dynamicType;
	}

	@Override
	public CIVLEnumType enumType(String name, Map<String, BigInteger> valueMap) {
		return new CommonEnumType(name, valueMap, universe.integerType());
	}

	@Override
	public CIVLFunctionType functionType(CIVLType returnType,
			CIVLType[] paraTypes) {
		return new CommonFunctionType(returnType, paraTypes,
				this.functionPointerSymbolicType);
	}

	@Override
	public CIVLHeapType heapType(String name) {
		return new CommonHeapType(name);
	}

	@Override
	public CIVLArrayType incompleteArrayType(CIVLType baseType) {
		return new CommonArrayType(baseType);
	}

	@Override
	public CIVLPrimitiveType integerType() {
		return integerType;
	}

	@Override
	public CIVLBundleType initBundleType() {
		return new CommonBundleType();
	}

	@Override
	public CIVLPointerType pointerType(CIVLType baseType) {
		return new CommonPointerType(baseType, pointerSymbolicType);
	}

	@Override
	public CIVLPrimitiveType processType() {
		return processType;
	}

	@Override
	public CIVLPrimitiveType realType() {
		return realType;
	}

	@Override
	public CIVLPrimitiveType scopeType() {
		return scopeType;
	}

	@Override
	public StructOrUnionField structField(Identifier name, CIVLType type) {
		return new CommonStructOrUnionField(name, type);
	}

	@Override
	public CIVLStructOrUnionType structOrUnionType(Identifier name,
			boolean isStruct) {
		return new CommonStructOrUnionType(name, isStruct);
	}

	@Override
	public CIVLPrimitiveType voidType() {
		return voidType;
	}

	@Override
	public CIVLHeapType heapType() {
		return this.heapType;
	}

	@Override
	public CIVLBundleType bundleType() {
		return this.bundleType;
	}

	@Override
	public void addSystemType(String name, CIVLType type) {
		this.systemTypes.put(name, type);
	}

	@Override
	public CIVLType systemType(String name) {
		return systemTypes.get(name);
	}

	@Override
	public CIVLCompleteDomainType completeDomainType(CIVLType rangeType, int dim) {
		return new CommonCompleteDomainType(rangeType, dim);
	}

	/* *********************************************************************
	 * SARL symbolic types
	 * *********************************************************************
	 */

	@Override
	public SymbolicUnionType bundleSymbolicType() {
		return this.bundleSymbolicType;
	}

	@Override
	public SymbolicTupleType dynamicSymbolicType() {
		return dynamicSymbolicType;
	}

	@Override
	public SymbolicTupleType functionPointerSymbolicType() {
		return functionPointerSymbolicType;
	}

	@Override
	public SymbolicTupleType heapSymbolicType() {
		return this.heapSymbolicType;
	}

	@Override
	public CIVLType rangeType() {
		return this.rangeType;
	}

	@Override
	public CIVLDomainType domainType(CIVLType rangeType) {
		if (this.domainType == null) {
			this.domainType = new CommonDomainType(rangeType);
		}
		return this.domainType;
	}

	@Override
	public SymbolicTupleType pointerSymbolicType() {
		return pointerSymbolicType;
	}

	@Override
	public SymbolicTupleType processSymbolicType() {
		return processSymbolicType;
	}

	@Override
	public SymbolicTupleType scopeSymbolicType() {
		return scopeSymbolicType;
	}

	/* *********************************************************************
	 * Special handling
	 * *********************************************************************
	 */
	@Override
	public void completeBundleType(CIVLBundleType bundleType,
			List<CIVLType> eleTypes, Collection<SymbolicType> elementTypes) {
		LinkedList<SymbolicType> arrayTypes = new LinkedList<SymbolicType>();
		SymbolicUnionType dynamicType;

		for (SymbolicType type : elementTypes)
			arrayTypes.add(universe.arrayType(type));
		dynamicType = universe.unionType(universe.stringObject("$bundle"),
				arrayTypes);
		dynamicType = (SymbolicUnionType) universe.canonic(dynamicType);
		bundleType.complete(eleTypes, elementTypes, dynamicType);
		this.bundleType = bundleType;
		this.bundleSymbolicType = dynamicType;
	}

	/* ************************** Private Methods ************************** */
	/**
	 * Computes the dynamic heap type, based on the list of malloc statements
	 * encountered in the model.
	 * 
	 * @param mallocStatements
	 *            The list of malloc statements in the model.
	 * @return The symbolic heap type.
	 */
	private SymbolicTupleType computeDynamicHeapType(
			Iterable<MallocStatement> mallocStatements) {
		LinkedList<SymbolicType> fieldTypes = new LinkedList<SymbolicType>();
		SymbolicTupleType result;

		for (MallocStatement statement : mallocStatements) {
			SymbolicType fieldType = universe.arrayType(statement
					.getDynamicObjectType());

			fieldTypes.add(fieldType);
		}
		result = universe.tupleType(universe.stringObject("$heap"), fieldTypes);
		result = (SymbolicTupleType) universe.canonic(result);
		return result;
	}

	/**
	 * Computes the symbolic initial value of a specified heap type.
	 * 
	 * @param heapDynamicType
	 *            The heap type to use.
	 * @return The initial value of the given help type.
	 */
	private SymbolicExpression computeInitialHeapValue(
			SymbolicTupleType heapDynamicType) {
		LinkedList<SymbolicExpression> fields = new LinkedList<SymbolicExpression>();
		SymbolicExpression result;

		for (SymbolicType fieldType : heapDynamicType.sequence()) {
			SymbolicArrayType arrayType = (SymbolicArrayType) fieldType;
			SymbolicType objectType = arrayType.elementType();
			SymbolicExpression emptyArray = universe.emptyArray(objectType);

			fields.add(emptyArray);
		}
		result = universe.tuple(heapDynamicType, fields);
		result = universe.canonic(result);
		return result;
	}

	/**
	 * Creates an instance of a CIVL primitive type, including void, integer,
	 * boolean, real, char, scope, process, and dynamic types.
	 * 
	 * @param kind
	 *            The kind of the primitive type. See also
	 *            {@link PrimitiveTypeKind}.
	 * @param dynamicType
	 *            The corresponding SARL symbolic type of the CIVL primitive
	 *            type.
	 * @return The CIVL primitive type of the given kind.
	 */
	private CIVLPrimitiveType primitiveType(PrimitiveTypeKind kind,
			SymbolicType dynamicType) {
		CIVLPrimitiveType result;
		NumericExpression size = null;
		BooleanExpression fact = null;

		if (dynamicType != null)
			dynamicType = (SymbolicType) universe.canonic(dynamicType);
		if (kind != PrimitiveTypeKind.VOID)
			size = sizeofPrimitiveType(kind);
		if (size == null)
			fact = universe.trueExpression();
		else
			fact = universe.lessThan(universe.zeroInt(), size);
		fact = (BooleanExpression) universe.canonic(fact);
		result = new CommonPrimitiveType(kind, dynamicType, size, fact);
		return result;
	}

	/**
	 * Create a new numeric expression for a sizeof expression of a certain
	 * primitive type.
	 * 
	 * @param kind
	 *            The kind of the primitive type of the sizeof expression.
	 * @return The numeric expression of the sizeof expression.
	 */
	private NumericExpression sizeofPrimitiveType(PrimitiveTypeKind kind) {
		String name = "SIZEOF_" + kind;
		NumericExpression result = (NumericExpression) universe
				.symbolicConstant(universe.stringObject(name),
						universe.integerType());

		if (!ModelConfiguration.RESERVE_NAMES.contains(name))
			ModelConfiguration.RESERVE_NAMES.add(name);
		result = (NumericExpression) universe.canonic(result);
		return result;
	}
}
