package edu.udel.cis.vsl.civl.model.IF;

import java.math.BigInteger;
import java.util.Collection;
import java.util.List;
import java.util.Map;

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
import edu.udel.cis.vsl.civl.model.IF.type.CIVLStructOrUnionType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.type.StructOrUnionField;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicUnionType;

/**
 * The CIVL type factory provides the CIVL primitive types, like
 * <code>$bool</code>, <code>int</code>, <code>float</code>, <code>$scope</code>
 * , etc. It also constructs the heap type and bundle type, which are
 * model-sensitive, and could be different from model to model.
 * 
 * @author Manchun Zheng (zmanchun)
 *
 */
public interface CIVLTypeFactory {

	/* ************************************************************************
	 * CIVL Types
	 * ************************************************************************
	 */

	/**
	 * Get the boolean primitive type.
	 * 
	 * @return The boolean primitive type.
	 */
	CIVLPrimitiveType booleanType();

	/**
	 * Returns the symbolic type of the bundle type.
	 * 
	 * @return the symbolic type of the bundle type.
	 */
	SymbolicUnionType bundleSymbolicType();

	/**
	 * Gets the CIVL bundle type, which is unique for a given CIVL model. A
	 * bundle type is a union type of all types referenced by a given CIVL
	 * model. A bundle type needs to be completed at the end of the construction
	 * of the model.
	 * 
	 * @return the CIVL bundle type of the model
	 */
	CIVLBundleType bundleType();

	/**
	 * Get the char primitive type.
	 * 
	 * @return The char primitive type.
	 */
	CIVLPrimitiveType charType();

	/**
	 * Returns a new complete array type with specified extent (length
	 * expression) and element type.
	 * 
	 * @param elementType
	 *            the type of each element in the array
	 * @param extent
	 *            the expression of integer type specifying the length of the
	 *            array
	 * @return the complete array type, as specified
	 */
	CIVLCompleteArrayType completeArrayType(CIVLType elementType,
			Expression extent);

	/**
	 * Creates a complete regular domain type, which is has the given dimension
	 * and is composed by the given range type.
	 * 
	 * @param rangeType
	 *            the range type
	 * @param dim
	 *            the dimension of the domain type
	 * @return the complete regular domain type.
	 */
	CIVLCompleteDomainType completeDomainType(CIVLType rangeType, int dim);

	/**
	 * This returns the universal domain type (<code>$domain</code>). It
	 * includes all the complete domain types (<code>$domain(n)</code>).
	 * 
	 * @param rangeType
	 * 
	 * @return the universal domain type
	 */
	CIVLDomainType domainType(CIVLType rangeType);

	/**
	 * Get the dynamic type.
	 * 
	 * @return The dynamic type.
	 */
	CIVLPrimitiveType dynamicType();

	/**
	 * Creates a new instance of enumeration type with the specified name.
	 * 
	 * @param name
	 *            The name of the enumeration type to be created.
	 * @param valueMap
	 *            The map of enumerator names and their values.
	 * @return The new enumeration type.
	 */
	CIVLEnumType enumType(String name, Map<String, BigInteger> valueMap);

	/**
	 * Creates a new instance of function type, which contains a return type and
	 * a list of parameter types.
	 * 
	 * @param returnType
	 *            The return type of the function type.
	 * @param paraTypes
	 *            The parameter types of the function type.
	 * @return the new function type
	 */
	CIVLFunctionType functionType(CIVLType returnType, CIVLType[] paraTypes);

	/**
	 * Returns a new, incomplete heap type. The heap type must be completed
	 * later by specifying a sequence of malloc statements in method
	 * {@link #completeHeapType}.
	 * 
	 * @param name
	 *            a name to give to the new heap type
	 * 
	 * @return a new incomplete heap type
	 */
	CIVLHeapType heapType(String name);

	/**
	 * Get a new incomplete array type.
	 * 
	 * @param elementType
	 *            The type of each element in the array.
	 * @return A new array type with the given base type.
	 */
	CIVLArrayType incompleteArrayType(CIVLType elementType);

	/**
	 * Create a new location. ======= Get the integer primitive type. >>>>>>>
	 * .r497
	 * 
	 * @return The integer primitive type.
	 */
	CIVLPrimitiveType integerType();

	/**
	 * Returns the CIVL heap type, which is unique for a given CIVL model. A
	 * heap type is a struct type of all types appearing in a malloc statement,
	 * plus all handled object types used by the model. A heap type needs to be
	 * completed at the end of the construction of the model.
	 * 
	 * @return the CIVL heap type
	 */
	CIVLHeapType heapType();

	/**
	 * Returns the symbolic heap type
	 * 
	 * @return the symbolic heap type
	 */
	SymbolicTupleType heapSymbolicType();

	/**
	 * Get a new pointer type.
	 * 
	 * @param baseType
	 *            The type pointed to by the pointer.
	 * @return A new pointer type with the given base type.
	 */
	CIVLPointerType pointerType(CIVLType baseType);

	/**
	 * Get the process type.
	 * 
	 * @return The process type.
	 */
	CIVLPrimitiveType processType();

	/**
	 * Returns the range type of the system.
	 * 
	 * @return the range type of the system.
	 * 
	 */
	CIVLType rangeType();

	/**
	 * Get the real primitive type.
	 * 
	 * @return The real primitive type.
	 */
	CIVLPrimitiveType realType();

	/**
	 * Get the scope primitive type.
	 * 
	 * @return The scope primitive type.
	 */
	CIVLPrimitiveType scopeType();

	/**
	 * Returns a new struct field, used to complete a struct type.
	 * 
	 * @param name
	 *            Identifier for the name of this struct member.
	 * @param type
	 *            The type of this struct member.
	 * @return A struct field with the given name and type.
	 */
	StructOrUnionField structField(Identifier name, CIVLType type);

	/**
	 * Returns new incomplete struct or union type with given name. Type can be
	 * completed later using one of the "complete" methods in
	 * CIVLStructOrUnionType.
	 * 
	 * The struct or union returned is a new instance of struct or union type
	 * that will never be equal to another struct or union type, regardless of
	 * identifier or fields.
	 * 
	 * @param name
	 *            identifier, usually the "tag" for this struct or union type
	 * @param isStruct
	 *            is the new type a struct type? If false, then the new type
	 *            will be a union type
	 * @return a new incomplete struct or union type with given name
	 */
	CIVLStructOrUnionType structOrUnionType(Identifier name, boolean isStruct);

	/**
	 * Obtains the CIVL type by the given name. This returns the type that has
	 * been added by {@link #addSystemType(String, CIVLType)}, and returns null
	 * if no such type.
	 * 
	 * @param name
	 *            The name (key) of the type.
	 * @return the CIVL type of the given name
	 */
	CIVLType systemType(String name);

	/**
	 * Returns the void type. Used in places where a type is required
	 * syntactically but there is no type, such as function which does not
	 * return a value.
	 * 
	 * @return The CIVL void type
	 */
	CIVLPrimitiveType voidType();

	/* ************************************************************************
	 * SARL symbolic types
	 * ************************************************************************
	 */

	/**
	 * Returns the symbolic type used to represent values of type
	 * CIVLDynamicType
	 * 
	 * @return the symbolic type used to represent values of type
	 *         CIVLDynamicType
	 */
	SymbolicTupleType dynamicSymbolicType();

	/**
	 * Gets the symbolic function pointer type.
	 * 
	 * @return the symbolic function pointer type.
	 */
	SymbolicTupleType functionPointerSymbolicType();

	/**
	 * Returns the symbolic type used to represent pointers.
	 * 
	 * @return he symbolic type used to represent pointers
	 */
	SymbolicTupleType pointerSymbolicType();

	/**
	 * Returns the symbolic type used to represent process reference values
	 * 
	 * @return the symbolic type used to represent process reference values
	 */
	SymbolicTupleType processSymbolicType();

	/**
	 * Returns the symbolic type used to represent scope values
	 * 
	 * @return the symbolic type used to represent scope values
	 */
	SymbolicTupleType scopeSymbolicType();

	/* ************************************************************************
	 * Special handling of types
	 * ************************************************************************
	 */

	/**
	 * Add the given type as the object type of one of the heap field. This will
	 * add one more element to the heap type.
	 * 
	 * @param type
	 * @param id
	 */
	void addHeapFieldObjectType(CIVLType type, int id);

	/**
	 * Added a type in map of system type, which is the map of types of system
	 * libraries, e.g., $gcomm/$comm for comm, $file for stdio,
	 * $gbarrier/$barrier for concurrency, etc. Each type that will be used by
	 * the system library components (e.g., library executor, etc) should be
	 * added explicitly by calling this method.
	 * 
	 * @param name
	 *            The name of the type.
	 * @param type
	 *            The type to be added as a system type
	 */
	void addSystemType(String name, CIVLType type);

	/**
	 * Completes the bundle type by specifying the list of all dynamic types
	 * which can occur as bundle elements. If the collections yields a sequence
	 * of types t_i, then the bundle symbolic type is union_i(array(t_i)).
	 * 
	 * @param bundleType
	 *            an incomplete bundle type
	 * @param eleTypes
	 *            the list of types that could be the element of the bundle type
	 * @param types
	 *            the set of all dynamic types which occur as bundle elements
	 */
	void completeBundleType(CIVLBundleType bundleType, List<CIVLType> eleTypes,
			Collection<SymbolicType> types);

	/**
	 * Completes the heap type.
	 * 
	 * @param heapType
	 *            an incomplete heap type
	 * @param mallocs
	 *            sequence of malloc statements that can access heaps of that
	 *            type
	 */
	void completeHeapType(CIVLHeapType heapType,
			Collection<MallocStatement> mallocs);

	/**
	 * Returns the type of the heap field of the given index. A CIVL model has
	 * its unique heap type, which has type of tuples of arrays of arrays of
	 * type, determined by malloc statements and handle types appear in the
	 * source program. For examples, given the following program,
	 * 
	 * <pre>
	 * int main(){
	 *   int* p = malloc(sizeof(int)*4);
	 *   $gcomm gcomm = $gcomm_create(...);
	 *   ...
	 * }
	 * </pre>
	 * 
	 * the heap type of the model of this program will be (int[][],
	 * __gcomm__[][]).
	 * 
	 * @param type
	 *            the type which is a field of the heap type
	 * @return the ID of the type in the heap
	 */
	int getHeapFieldId(CIVLType type);

	/**
	 * Initializes the bundle type of the model and return the result.
	 * 
	 * @return The new initial bundle type.
	 */
	CIVLBundleType initBundleType();

}
