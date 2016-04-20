package edu.udel.cis.vsl.civl.dynamic.IF;

import java.util.Iterator;
import java.util.List;

import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.expr.ArrayElementReference;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicSequence;

/**
 * A SymbolicUtility provides all the common operations of symbolic expressions.
 * 
 * @author Manchun Zheng
 * 
 */
public interface SymbolicUtility {
	/**
	 * Constructs the string representation of an array of characters, which
	 * contains at least one '\0' character, starting from the given index and
	 * ending at the index of '\0' minus one. If the result is to be printed,
	 * then special characters like '\r', '\t', etc, will be replaced as the
	 * actual string representation "\\r", "\\t", etc.
	 * 
	 * For example, given an character array {'a', 'b', '\t', 'c', 'd', '\n',
	 * '\0'}, if starting index is 1, and is it not for print, then the result
	 * string will be "b\tcd\n"; if it is for print, then the result string is
	 * "b\\tcd\\n".
	 *
	 * 
	 * @param source
	 *            The source code information for error report.
	 * @param charArray
	 *            The character array in the representation of symbolic sequence
	 * @param startIndex
	 *            The index in the character array where the string starts
	 * @param forPrint
	 *            Will the result be printed? If yes, then special characters
	 *            need to be handled specifically, e.g., '\n' becomes "\\n".
	 * @return the string representation from the given character array with
	 */
	StringBuffer charArrayToString(CIVLSource source,
			SymbolicSequence<?> charArray, int startIndex, boolean forPrint);

	/**
	 * Checks if the object that the container pointer points to contains that
	 * of the element pointer.
	 * 
	 * @param container
	 *            The pointer that is expected to contain the object of the
	 *            element pointer.
	 * @param element
	 *            The element pointer.
	 * @return True iff the object that the first pointer points to contains
	 *         that of the send pointer.
	 */
	BooleanExpression contains(SymbolicExpression container,
			SymbolicExpression element);

	/**
	 * Given a symbolic type, returns a canonic symbolic expression which
	 * somehow wraps that type so it can be used as a value. Nothing should be
	 * assumed about the symbolic expression. To extract the type from such an
	 * expression, use method {@link #getType}.
	 * 
	 * @param type
	 *            a symbolic type
	 * @return a canonic symbolic expression wrapping that type
	 */
	SymbolicExpression expressionOfType(SymbolicType type);

	/**
	 * 
	 * Gets a Java concrete int from a symbolic expression or throws exception.
	 * 
	 * @param source
	 *            source code information for error report
	 * @param expression
	 *            a numeric expression expected to hold concrete int value
	 * @return the concrete int
	 * @throws CIVLInternalException
	 *             if a concrete integer value cannot be extracted
	 */
	int extractInt(CIVLSource source, NumericExpression expression);

	/**
	 * Gets a concrete Java int from the field of a symbolic expression of tuple
	 * type or throws exception.
	 * 
	 * @param source
	 *            source code information for error report
	 * @param tuple
	 *            symbolic expression of tuple type
	 * @param fieldIndex
	 *            index of a field in that tuple
	 * @return the concrete int value of that field
	 * @throws CIVLInternalException
	 *             if a concrete integer value cannot be extracted
	 */
	int extractIntField(CIVLSource source, SymbolicExpression tuple,
			IntObject fieldIndex);

	/**
	 * <p>
	 * Given a pointer to a certain element of some array, returns the index of
	 * the element that the pointer points to.
	 * </p>
	 * 
	 * <p>
	 * Precondition: pointer must point to an element of some array.
	 * </p>
	 * 
	 * @param source
	 *            The source code information for error report.
	 * @param pointer
	 *            The pointer checks.
	 * @return The index of the element that the pointer points to.
	 */
	int getArrayIndex(CIVLSource source, SymbolicExpression pointer);

	/**
	 * Given a pointer value, returns the dynamic scope ID component of that
	 * pointer value.
	 * 
	 * @param source
	 *            the source code information for error report.
	 * @param pointer
	 *            a pointer value
	 * @return the dynamic scope ID component of that pointer value
	 */
	int getDyscopeId(CIVLSource source, SymbolicExpression pointer);

	/**
	 * Given a pointer value, returns the symbolic reference component of that
	 * value. The "symRef" refers to a sub-structure of the variable pointed to.
	 * 
	 * @param pointer
	 *            a pointer value
	 * @return the symRef component
	 */
	ReferenceExpression getSymRef(SymbolicExpression pointer);

	/**
	 * Returns the pointer value obtained by replacing the symRef component of
	 * the given pointer value with the given symRef.
	 * 
	 * @param pointer
	 *            a pointer value
	 * @param symRef
	 *            a symbolic reference expression
	 * @return the pointer obtained by modifying the given one by replacing its
	 *         symRef field with the given symRef
	 */
	SymbolicExpression setSymRef(SymbolicExpression pointer,
			ReferenceExpression symRef);

	/**
	 * Given a pointer value, returns the variable ID component of that value.
	 * 
	 * @param source
	 *            the source code information for error report.
	 * @param pointer
	 *            a pointer value
	 * @return the variable ID component of that value
	 */
	int getVariableId(CIVLSource source, SymbolicExpression pointer);

	/**
	 * <p>
	 * Returns the heap memory unit involved by the given pointer.
	 * </p>
	 * 
	 * @param pointer
	 *            A valid pointer that points to some part of a heap.
	 * @return A pointer to a heap object that is involved by the given pointer.
	 */
	SymbolicExpression heapMemUnit(SymbolicExpression pointer);

	/**
	 * Constructs an invalid heap object of a certain type. A heap object
	 * becomes invalid when it gets deallocated.
	 * 
	 * @param heapObjectType
	 *            The type of the heap object.
	 * @return The invalid heap object of the given type.
	 */
	SymbolicConstant invalidHeapObject(SymbolicType heapObjectType);

	/**
	 * Checks if the components (either a complete object or a sub-component of
	 * an object) that the two pointers point to have no intersection.
	 * 
	 * @param pointer1
	 *            The first pointer.
	 * @param pointer2
	 *            The second pointer.
	 * @return True iff there is no intersection between the components that the
	 *         given two pointers point to.
	 */
	boolean isDisjointWith(SymbolicExpression pointer1,
			SymbolicExpression pointer2);

	/**
	 * Checks if a heap is empty, i.e., either it is the SARL null expression or
	 * all heap objects it holds are marked as INVALID (already deallocated).
	 * 
	 * @param heapValue
	 *            The value of the heap to be checked.
	 * @return True iff the heap has null value or is empty.
	 */
	boolean isEmptyHeap(SymbolicExpression heapValue);

	/**
	 * Is the given pointer the result of some malloc/handle create operation?
	 * 
	 * @param source
	 *            The source code information for error report.
	 * @param pointer
	 *            The pointer to be checked.
	 * @return True iff the given pointer is the result of some malloc/handle
	 *         create operation.
	 */
	boolean isMallocPointer(CIVLSource source, SymbolicExpression pointer);

	/**
	 * Checks if a given value is initialized.
	 * 
	 * @param value
	 *            The value to be checked.
	 * @return True iff the value is already initialized.
	 */
	boolean isInitialized(SymbolicExpression value);

	/**
	 * Checks if the given value is within the index-th range of a certain
	 * rectangular domain.
	 * 
	 * @param value
	 *            The value to be tested if it is in range.
	 * @param domain
	 *            The rectangular domain that the value wants to test with.
	 * @param index
	 *            The index of the range that the test bases on.
	 * @return True iff the given value is within the index-th range of a
	 *         certain domain.
	 */
	BooleanExpression isInRange(SymbolicExpression value,
			SymbolicExpression range);

	/**
	 * Is this heap object invalid?
	 * 
	 * @param heapObject
	 *            The heap object.
	 * @return True iff the given heap object is invalid.
	 */
	boolean isInvalidHeapObject(SymbolicExpression heapObject);

	/**
	 * Checks if a given pointer is a NULL pointer.
	 * 
	 * @param pointer
	 *            The pointer to be checked.
	 * @return True iff the given pointer is NULL.
	 */
	boolean isNullPointer(SymbolicExpression pointer);

	/**
	 * Is the given pointer pointing to a memory space that is part of a heap?
	 * 
	 * @param pointer
	 *            The pointer to be tested.
	 * 
	 * @return True iff the pointer points to a certain part of some heap.
	 */
	boolean isHeapPointer(SymbolicExpression pointer);

	/**
	 * Is this an undefined pointer?
	 * 
	 * @param pointer
	 *            The pointer.
	 * @return True iff the given pointer is undefined.
	 */
	boolean isUndefinedPointer(SymbolicExpression pointer);

	/**
	 * Checks if a pointer is valid for dereference, i.e., it isn't NULL, nor is
	 * it pointing to a deallocated memory space, nor does it point to a memory
	 * unit of an invalid scope.
	 * 
	 * @param pointer
	 *            The pointer to be checked.
	 * @return True iff the pointer is valid, i.e., can be dereferenced.
	 */
	boolean isValidPointer(SymbolicExpression pointer);

	/**
	 * Checks if the given reference is valid for a certain object or a
	 * sub-component of some object.
	 * 
	 * @param ref
	 *            The reference.
	 * @param component
	 *            The given component which can be an object or a sub-component
	 *            of an object.
	 * @return True iff the given reference expression is applicable for the
	 *         given object.
	 */
	boolean isValidRefOf(ReferenceExpression ref, SymbolicExpression component);

	/**
	 * Makes a pointer value from the given dynamic scope ID, variable ID, and
	 * symbolic reference value.
	 * 
	 * @param dyscopeId
	 *            ID number of a dynamic scope
	 * @param varId
	 *            ID number of a variable within that scope
	 * @param symRef
	 *            a symbolic reference to a point within the variable
	 * @return a pointer value as specified by the 3 components
	 */
	SymbolicExpression makePointer(int dyscopeId, int varId,
			ReferenceExpression symRef);

	/**
	 * Constructs a new pointer by replacing the reference expression of a given
	 * pointer. For example, given a pointer &a[5] and a reference [0], the
	 * result will be &a[0]. The given pointer can refer to a heap object, in
	 * which case, the heap object reference is considered the old "variable"
	 * and will remain the same.
	 * 
	 * @param oldPointer
	 *            The old pointer whose reference expression will be changed.
	 * @param symRef
	 *            The new reference expression to be used for the new pointer.
	 * @return the new pointer which refers to the same variable/heap object as
	 *         the given pointer, but with a new reference expression.
	 */
	SymbolicExpression makePointer(SymbolicExpression oldPointer,
			ReferenceExpression symRef);

	/**
	 * * Constructs a pointer by combining a pointer to a component, either an
	 * object (a heap atomic object or a normal object) or a sub-component of an
	 * object, and a reference expression w.r.t that component.
	 * 
	 * @param componentPointer
	 *            a pointer to a component
	 * @param reference
	 *            a reference expression
	 * @return A new pointer by combining the component pointer and the given
	 *         reference w.r.t. that component.
	 */
	SymbolicExpression extendPointer(SymbolicExpression componentPointer,
			ReferenceExpression reference);

	/**
	 * Creates a new array of given length, using the given type as its element
	 * type, and each element having the given value.
	 * 
	 * @param context
	 *            The context of the operation, i.e., the path condition of the
	 *            current state.
	 * @param elementValueType
	 *            The type of the array element. Note necessarily the type of
	 *            <code>eleValue</code>.
	 * @param length
	 *            The length of the array.
	 * @param eleValue
	 *            The element value of the array.
	 * @return
	 */
	SymbolicExpression newArray(BooleanExpression context,
			SymbolicType elementValueType, NumericExpression length,
			SymbolicExpression eleValue);

	/**
	 * Returns the NULL pointer of CIVL.
	 * 
	 * @return The NULL pointer of CIVL.
	 */
	SymbolicExpression nullPointer();

	/**
	 * Given a non-trivial pointer, i.e., a pointer to some location inside an
	 * object, returns the parent pointer. For example, a pointer to an array
	 * element returns the pointer to the array.
	 * 
	 * @param pointer
	 *            non-trivial pointer
	 * @return pointer to parent
	 * @throws CIVLInternalException
	 *             if pointer is trivial
	 */
	SymbolicExpression parentPointer(CIVLSource source,
			SymbolicExpression pointer);

	/**
	 * Computes the reference expression of a pointer. If the pointer is
	 * pointing to some part of the heap, then the reference expression is the
	 * reference expression w.r.t the corresponding heap atomic object;
	 * otherwise, it is the original reference expression of the pointer.
	 * 
	 * @param pointer
	 *            The pointer to whose reference is to be computed.
	 * @return The reference expression of the pointer w.r.t the object it
	 *         points to.
	 */
	ReferenceExpression referenceOfPointer(SymbolicExpression pointer);

	/**
	 * Computes the reference expression of a given heap pointer w.r.t the
	 * corresponding heap object.
	 * 
	 * @param heapPointer
	 *            The heap pointer.
	 * @return The reference expression of a given pointer w.r.t the
	 *         corresponding heap memory unit.
	 */
	ReferenceExpression referenceToHeapMemUnit(SymbolicExpression heapPointer);

	/**
	 * Compute the symbolic representation of the size of a given symbolic type.
	 * 
	 * @param source
	 *            The source code element to be used in the error report (if
	 *            any).
	 * @param type
	 *            The symbolic type whose size is to evaluated.
	 * @return The symbolic representation of the size of the symbolic type.
	 */
	NumericExpression sizeof(CIVLSource source, SymbolicType type);

	/**
	 * Returns the abstract function <code>sizeof()</code>.
	 * 
	 * @return The abstract function <code>sizeof()</code>.
	 */
	SymbolicExpression sizeofFunction();

	/**
	 * Returns an array element reference by giving the array reference and the
	 * coordinates to indexing the element.
	 * 
	 * This function makes the {@link ArrayElementReference} based on the given
	 * array reference. For example, for an array "int a[2][3][4]", giving the
	 * reference to "a[1]" and an indices array {1,2}, it returns the new
	 * reference to "a[1][1][2]".
	 * 
	 * @author Ziqing Luo
	 * @param arrayReference
	 *            An reference to an array
	 * @param newIndices
	 *            indexes for referencing the element
	 * @return the new arrayElementReference
	 */
	ReferenceExpression makeArrayElementReference(
			ReferenceExpression arrayReference, NumericExpression[] newIndices);

	/**
	 * Returns the undefined pointer of CIVL, which is a tuple <-2, -2, NULL>.
	 * In CIVL, a pointer becomes undefined when the memory space it points to
	 * get deallocated.
	 * 
	 * @return The undefined pointer.
	 */
	SymbolicExpression undefinedPointer();

	/* ****************** Domain Operation section ********************* */

	/**
	 * Returns true if and only if the domain is more precisely a rectangular
	 * domain.
	 * 
	 * @param domain
	 *            The symbolic expression of a domain object
	 * @return
	 */
	boolean isRecDomain(SymbolicExpression domain);

	/**
	 * Returns true if and only if the domain is more precisely a literal
	 * domain.
	 * 
	 * @param domain
	 *            The symbolic expression of a domain object
	 * @return
	 */
	boolean isLiteralDomain(SymbolicExpression domain);

	/**
	 * Get the first element of a domain. Return null if domain is empty.
	 * 
	 * @param domValue
	 *            The domain object which will contribute a first element.
	 * @return
	 */
	List<SymbolicExpression> getDomainInit(SymbolicExpression domValue);

	/**
	 * Computes the size of a domain, that is the number of elements contained
	 * in the domain.
	 * 
	 * @param domain
	 *            The symbolic expression of domain.
	 * @return The number of elements contained in the domain.
	 */
	NumericExpression getDomainSize(SymbolicExpression domain);

	/**
	 * Get the type of elements of domain which are also elements of literal
	 * domain object. For an N dimensional domain, the element type should be an
	 * array of integers of length of N, i.e. <code>int [N]</code>.
	 * 
	 * @param domain
	 *            The symbolic expression of a domain object
	 * @return domain element type
	 * 
	 */
	SymbolicType getDomainElementType(SymbolicExpression domain);

	/**
	 * Return a iterator for a domain object. (This function can be applied on
	 * all domain types)
	 * 
	 * @param domain
	 *            The symbolic expression of the domain object.
	 * @return
	 */
	Iterator<List<SymbolicExpression>> getDomainIterator(
			SymbolicExpression domain);

	/**
	 * Get the subsequence of the given element of the domain.
	 * 
	 * @param domValue
	 *            The symbolic expression of the rectangular domain field.
	 * @param varValues
	 *            The given current domain element.
	 * @param concreteDim
	 *            The dimension of domain.
	 * @return
	 */
	List<SymbolicExpression> getNextInRecDomain(SymbolicExpression recDomUnion,
			List<SymbolicExpression> varValues, int concreteDim);

	/**
	 * Check if the given domain element has a subsequence in the given
	 * rectangular domain.
	 * 
	 * @param recDomainUnion
	 *            The rectangular domain union object.
	 * @param concreteDim
	 *            The number of the dimension of the domain
	 * @param domElement
	 *            The element of the domain
	 * @return
	 */
	boolean recDomainHasNext(SymbolicExpression recDomainUnion,
			int concreteDim, List<SymbolicExpression> domElement);

	/**
	 * Iterating a literal domain to match a given domain element. Returns the
	 * index of the element.
	 * 
	 * @param literalDomain
	 *            The symbolic expression of the literal domain union field
	 * @param literalDomElement
	 *            The given element will be matched
	 * @param dim
	 *            The dimension of the literal domain
	 * @return the index of the element in the domain or -1 which means the
	 *         given element is not a member of the domain.
	 */
	int literalDomainSearcher(SymbolicExpression literalDomain,
			List<SymbolicExpression> literalDomElement, int dim);

	/**
	 * Returns true if and only if the given domain is empty which means there
	 * is no elements in the domain.
	 * 
	 * @param domain
	 *            The symbolic expression of the domain object.
	 * @param dim
	 *            The concrete number of dimension of the domain. It's only
	 *            significant when the domain is a rectangular domain.
	 * @param source
	 *            The CIVL source of the statement involves this empty checking
	 *            operation.
	 * @return
	 */
	boolean isEmptyDomain(SymbolicExpression domain, int dim, CIVLSource source);

	/* ****************** End of Domain Operation section ********************* */
	/**
	 * pre-condition:
	 * <ol>
	 * <li>"coordinateSizes" must not be null</li>
	 * </ol>
	 * post-condition:
	 * <ol>
	 * <li>the returned {@link CIVLType} must not be null</li>
	 * </ol>
	 * Computing sizes of all slices of the given array. Here an array slice is
	 * a sub-array with a lower dimension of the given array.
	 * 
	 * @param coordinateSizes
	 *            Sizes of coordinates representing an array. e.g. {2,3,4}
	 *            stands for an array T a[2][3][4].
	 * @return Sizes of all array slices. e.g. input:{2,3,4} ==> output:{12, 4,
	 *         1}
	 * @throws UnsatisfiablePathConditionException
	 */
	NumericExpression[] arraySlicesSizes(NumericExpression[] coordinateSizes)
			throws UnsatisfiablePathConditionException;

	/**
	 * pre-condition:
	 * <ol>
	 * <li>"arrayPtr" must not be "null"</li>
	 * </ol>
	 * post-condition:
	 * <ol>
	 * <li>the returned object must not be "null"</li>
	 * </ol>
	 * Get the most ancestor pointer of the given array element reference
	 * pointer.
	 * 
	 * @param arrayPtr
	 *            An array element reference pointer or a pointer to an array
	 * @param source
	 *            The CIVL source of the pointer
	 * @return
	 */
	SymbolicExpression arrayRootPtr(SymbolicExpression arrayPtr,
			CIVLSource source);

	/**
	 * Returns an array of indices in the given {@link ArrayElementReference}.
	 * Note: The order of indices is from right to left which is same as the
	 * visual expression order.
	 * 
	 * @param eleRef
	 *            A reference of element of an array
	 * @return
	 */
	NumericExpression[] stripIndicesFromReference(ArrayElementReference eleRef);

	/**
	 * Computes size of each coordinate of a given array. Returns an Java Array
	 * of those coordinate sizes which are in the same order as the array being
	 * declared.<br>
	 * For example, giving an array "int a[2][3][4]" returns {2, 3, 4}.
	 * 
	 * @param array
	 *            The target array.
	 * @return The Java Array contains array extents information.
	 */
	NumericExpression[] arrayCoordinateSizes(SymbolicCompleteArrayType arrayType);

	/**
	 * This function does an arithmetic integer division, returns the quotient
	 * and remainder
	 * 
	 * @param dividend
	 *            The {@link NumericExpression} of the quotient, must be a
	 *            Integer number
	 * @param denominator
	 *            The {@link NumericExpression} of the denominator, must be a
	 *            Integer number
	 * @return A {@link Pair} of quotient (left) and remainder (right)
	 */
	public Pair<NumericExpression, NumericExpression> arithmeticIntDivide(
			NumericExpression dividend, NumericExpression denominator);
}
