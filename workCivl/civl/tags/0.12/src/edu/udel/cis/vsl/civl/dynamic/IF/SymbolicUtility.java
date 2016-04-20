package edu.udel.cis.vsl.civl.dynamic.IF;

import java.util.List;

import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.sarl.IF.expr.ArrayElementReference;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
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
	 * 
	 * Gets a Java concrete int from a symbolic expression or throws exception.
	 * 
	 * @param expression
	 *            a numeric expression expected to hold concrete int value
	 * @return the concrete int
	 * @throws CIVLInternalException
	 *             if a concrete integer value cannot be extracted
	 */
	int extractInt(CIVLSource source, NumericExpression expression);

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
	 *            a symbolic refererence expression
	 * @return the pointer obtained by modifying the given one by replacing its
	 *         symRef field with the given symRef
	 */
	SymbolicExpression setSymRef(SymbolicExpression pointer,
			ReferenceExpression symRef);

	/**
	 * Given a pointer value, returns the dynamic scope ID component of that
	 * pointer value.
	 * 
	 * @param pointer
	 *            a pointer value
	 * @return the dynamic scope ID component of that pointer value
	 */
	int getDyscopeId(CIVLSource source, SymbolicExpression pointer);

	/**
	 * Given a pointer value, returns the variable ID component of that value.
	 * 
	 * @param pointer
	 *            a pointer value
	 * @return the variable ID component of that value
	 */
	int getVariableId(CIVLSource source, SymbolicExpression pointer);

	/**
	 * Gets a concrete Java int from the field of a symbolic expression of tuple
	 * type or throws exception.
	 * 
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
	 * Given an array, a start index, and end index, returns the array which is
	 * the subsequence of the given array consisting of the elements in
	 * positions start index through end index minus one. The length of the new
	 * array is endIndex - startIndex. TODO move to libcivlc?
	 * 
	 * @param array
	 * @param startIndex
	 * @param endIndex
	 * @param assumption
	 * @param source
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	SymbolicExpression getSubArray(SymbolicExpression array,
			NumericExpression startIndex, NumericExpression endIndex,
			State state, String process, CIVLSource source)
			throws UnsatisfiablePathConditionException;

	/**
	 * Compute the symbolic representation of the size of a given symbolic type.
	 * 
	 * @param source
	 *            The source code element to be used in the error report (if
	 *            any).
	 * @param type
	 *            The symbolic type whose size is to evaluated.
	 * @return The symbolic representation of the symbolic type.
	 */
	NumericExpression sizeof(CIVLSource source, SymbolicType type);

	/**
	 * Returns the abstract function <code>sizeof()</code>.
	 * 
	 * @return The abstract function <code>sizeof()</code>.
	 */
	SymbolicExpression sizeofFunction();

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
	 * Returns the initial value of a(n) (empty) heap.
	 * 
	 * @return The initial value of a(n) (empty) heap.
	 */
	SymbolicExpression initialHeapValue();

	/**
	 * Makes a pointer value from the given dynamic scope ID, variable ID, and
	 * symbolic reference value.
	 * 
	 * @param scopeId
	 *            ID number of a dynamic scope
	 * @param varId
	 *            ID number of a variable within that scope
	 * @param symRef
	 *            a symbolic reference to a point within the variable
	 * @return a pointer value as specified by the 3 components
	 */
	SymbolicExpression makePointer(int scopeId, int varId,
			ReferenceExpression symRef);

	/**
	 * Computes the user-friendly string representation of a state.
	 * 
	 * @param state
	 *            The state whose string representation is to be computed.
	 * @return The user-friendly string representation of a state.
	 */
	StringBuffer stateToString(State state);

	/**
	 * <p>
	 * Computes the user-friendly string representation of a symbolic
	 * expression.
	 * </p>
	 * 
	 * <p>
	 * If the given expression is a pointer, then its string representation is
	 * computed according to the object that it refers to:
	 * <ul>
	 * <li>a variable: <code>& variable &lt;dyscope name></code>; <br>
	 * e.g.,
	 * 
	 * <pre>
	 * int a = 9; int * p = &a;
	 * </pre>
	 * 
	 * The representation of <code>p</code> would be <code>&a&lt;d0></code>
	 * assuming that the name of the dynamic scope of <code>a</code> is
	 * <code>d0</code>.</li>
	 * <li>an element of an array: <code>&array&lt;dyscope name>[index]</code>;<br>
	 * e.g.,
	 * 
	 * <pre>
	 * int a[5]; int *p = &a[1];
	 * </pre>
	 * 
	 * The representation of <code>p</code> would be <code>&a&lt;d0>[1]</code>
	 * assuming that the name of the dynamic scope of <code>a</code> is
	 * <code>d0</code>.</li>
	 * <li>a field of a struct: <code>&struct&lt;dyscope name>.field</code>;<br>
	 * e.g.,
	 * 
	 * <pre>
	 * typedef struct {int x; int y;} A; A s; int*p = &s.y;
	 * </pre>
	 * 
	 * The representation of p would be <code>&a&lt;d0>.y</code> assuming that
	 * the name of the dynamic scope of <code>a</code> is <code>d0</code>.</li>
	 * 
	 * <li>a heap cell:
	 * <code>heapObject&lt;dyscope name, malloc ID, number of malloc call></code>
	 * .</li>
	 * </ul>
	 * </p>
	 * 
	 * @param source
	 *            The source code information related to the symbolic expression
	 *            for error erport if any.
	 * @param state
	 *            The state that the symbolic expression belongs to.
	 * @param symbolicExpression
	 *            The symbolic expression whose string representation is to be
	 *            computed.
	 * @return The user-friendly string representation of a state.
	 */
	String symbolicExpressionToString(CIVLSource source, State state,
			SymbolicExpression symbolicExpression);

	/**
	 * Constructs the string representation of an array of characters.
	 * 
	 * @param source
	 * @param charArray
	 * @param startIndex
	 * @param forPrint
	 * @return
	 */
	StringBuffer charArrayToString(CIVLSource source,
			SymbolicSequence<?> charArray, int startIndex, boolean forPrint);

	int getArrayIndex(CIVLSource source, SymbolicExpression charPointer);

	/* ***************** Arrays Operations Utilities ******************** */
	/**
	 * Recursively updates the array references for an multi-dimensional array
	 * by using a set of indexes and a given reference to an array element. e.g.
	 * If the arrayReference is a[x][y], then the size of newIndexes should be
	 * 2. And newIndexes[0] corresponds to update the x, newIndexes[1]
	 * corresponds to update the y, and so forth.
	 * 
	 * @author Ziqing Luo
	 * @param arrayReference
	 *            An reference to an array
	 * @param newIndexes
	 *            indexes for referencing the element
	 * @return the new arrayElementReference
	 */
	public SymbolicExpression updateArrayElementReference(
			ArrayElementReference arrayReference,
			List<NumericExpression> newIndexes);

	/**
	 * Unrolling a given array to a ordered list of elements of that array(Here
	 * element should never be array type any more). <br>
	 * 
	 * e.g. 1 For an array <code>int a[2][2] = {1,2,3,4}</code>, the unrolled
	 * list will be <code>{1,2,3,4}</code>
	 * 
	 * e.g. 2. Given a variable <code> int a = 1;</code>, this function will
	 * give you an unrolled list <code>{1}</code>.
	 * 
	 * @author Ziqing Luo
	 * 
	 * @param state
	 *            The current state
	 * @param process
	 *            The identifier of the process
	 * @param array
	 *            The given array.(Or can be a single object, but by intention,
	 *            this function is mainly for multi-dimensional arrays)
	 * @param civlsource
	 *            The CIVL source of the given array.
	 * @return
	 */
	public SymbolicExpression arrayUnrolling(State state, String process,
			SymbolicExpression array, CIVLSource civlsource);

	/**
	 * Casting an array to a new array with the given array type.<br>
	 * 
	 * Pre-Condition: <br>
	 * 1. The old array should be a complete array (or a object is allowed).<br>
	 * 
	 * 2. The cast should be a legal cast. <br>
	 * 
	 * 
	 * Special cases:<br>
	 * If the array(the "oldArray") is not an array type, return the object (the
	 * "oldArray") immediately.<br>
	 * If the given type is not an array type( but the "oldArray" is an array
	 * type), the length of the "oldArray" must be one, then return the first
	 * element of the "oldArray". Else, return null<br>
	 * 
	 * 
	 * @param state
	 *            The current state
	 * @param process
	 *            The identifier of the process
	 * @param oldArray
	 *            The array needs being casted.
	 * @param type
	 *            The given type that the "oldArray" will try to cast to.
	 * @param civlsource
	 *            The CIVL source of the given array.
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	public SymbolicExpression arrayCasting(State state, String process,
			SymbolicExpression array, SymbolicType type, CIVLSource civlsource)
			throws UnsatisfiablePathConditionException;

	/* ********************************************************************* */
	/**
	 * Checks if a heap is null or empty.
	 * 
	 * @param heapValue
	 *            The value of the heap to be checked.
	 * @return True iff the heap has null value or is empty.
	 */
	boolean isEmptyHeap(SymbolicExpression heapValue);

	SymbolicExpression rangeOfDomainAt(SymbolicExpression domain, int index);

	SymbolicExpression initialValueOfRange(SymbolicExpression range,
			boolean isLast);

	BooleanExpression isInRange(SymbolicExpression value,
			SymbolicExpression domain, int index);

	SymbolicExpression rangeIncremental(SymbolicExpression value,
			SymbolicExpression range);

	SymbolicExpression getLowOfDomainAt(SymbolicExpression domain, int index);

	NumericExpression getRangeSize(SymbolicExpression range);

	NumericExpression getLowOfRange(SymbolicExpression range);

	NumericExpression getHighOfRange(SymbolicExpression range);

	NumericExpression getStepOfRange(SymbolicExpression range);

	boolean isInitialized(SymbolicExpression value);

	SymbolicExpression contains(SymbolicExpression first,
			SymbolicExpression second);

	SymbolicExpression nullPointer();

	boolean isNullPointer(SymbolicExpression pointer);

	boolean isHeapObjectDefined(SymbolicExpression heapObj);

	/**
	 * Is the given pointer pointing to a memory space that is part of a heap?
	 * 
	 * @param pointer
	 * @return
	 */
	boolean isHeapPointer(SymbolicExpression pointer);

	/**
	 * Gets the pointer to the heap of the given scope.
	 * 
	 * @param source
	 *            The source code information for error report.
	 * @param state
	 *            The state where this operation happens.
	 * @param process
	 *            The information of the process that triggers this operation,
	 *            for the purpose of error report.
	 * @param scopeValue
	 *            The scope value
	 * @return The pointer to the heap of the given scope.
	 * @throws UnsatisfiablePathConditionException
	 *             if the given scope is not concrete or not a valid scope.
	 */
	SymbolicExpression heapPointer(CIVLSource source, State state,
			String process, SymbolicExpression scopeValue)
			throws UnsatisfiablePathConditionException;

	/**
	 * Is the given pointer pointing to the first element of a heap cell?
	 * 
	 * @param source
	 * @param pointer
	 * @return
	 */
	boolean isHeapObjectPointer(CIVLSource source, SymbolicExpression pointer);

	/**
	 * Gets the heap cell pointer of a heap object pointer.
	 * 
	 * @param heapObjectPointer
	 * @return
	 */
	SymbolicExpression heapCellPointer(SymbolicExpression heapObjectPointer);

	ReferenceExpression referenceOfPointer(SymbolicExpression pointer);

	SymbolicExpression makePointer(SymbolicExpression objectPointer,
			ReferenceExpression reference);

	boolean isValidRefOf(ReferenceExpression ref, SymbolicExpression value);

	CIVLType typeOfObjByPointer(CIVLSource soruce, State state,
			SymbolicExpression pointer);

	boolean isUndefinedConstant(SymbolicExpression value);

	boolean isDisjointWith(SymbolicExpression pointer1,
			SymbolicExpression pointer2);
}
