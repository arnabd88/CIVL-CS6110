package edu.udel.cis.vsl.civl.semantics.IF;

import java.util.Map;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * This class provides methods dealing with symbolic expressions and states,
 * which represent some common-used operations like obtaining a sub-array from a
 * given array, etc.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public interface SymbolicAnalyzer {
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
	 *            for error report if any.
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
	 * Computes the CIVL type of the object referring to by the given pointer.
	 * 
	 * @param soruce
	 *            The source code information related to the symbolic expression
	 *            for error report if any.
	 * @param state
	 *            The state that the given pointer belongs to.
	 * @param pointer
	 *            The pointer the type of whose object is to be computed.
	 * @return The CIVL type of the object referring to by the given pointer.
	 */
	CIVLType typeOfObjByPointer(CIVLSource soruce, State state,
			SymbolicExpression pointer);

	/**
	 * Get the type of the non-array element of an array by given a pointer to
	 * an array
	 * 
	 * @param array
	 * @return the type of the non-array element of an array
	 */
	CIVLType getFlattenedArrayElementType(State state, CIVLSource source,
			SymbolicExpression arrayPtr);

	/**
	 * Computes the array element indexes in an array element reference.<br>
	 * Indexes are stored in a map whose keys indicate the dimension of the
	 * array. Here 0 marks the deepest dimension and 1 marks the second deepest
	 * dimension and so forth.
	 * 
	 * @param state
	 *            The current state
	 * @param source
	 *            The CIVL source of the pointer
	 * @param pointer
	 *            The array element reference pointer
	 * @param ignoreDiffBetweenHeapAndArray
	 *            flag indicates if returning all indexes from a pointer to heap
	 *            object. Since in CIVL, heap is represented as two dimensional
	 *            array which may be lumped with nested array incorrectly. Set
	 *            this flag to false, this function will ignore the difference
	 *            between heap and nested arrays(which currently is just used by
	 *            pointer subtraction).
	 * @return
	 */
	Map<Integer, NumericExpression> arrayIndexesByPointer(State state,
			CIVLSource source, SymbolicExpression pointer,
			boolean ignoreDiffBetweenHeapAndArray);

	// TODO: need a better name
	/**
	 * Cast an pointer to the deepest array element reference pointer if the
	 * pointed object is an array.
	 * 
	 * @author Ziqing Luo
	 * @param state
	 *            The current state
	 * @param process
	 *            The information of the process
	 * @param pointer
	 *            The pointer needs being casted
	 * @param source
	 *            The CIVL source of the pointer
	 * @return The casted pointer
	 * @throws UnsatisfiablePathConditionException
	 */
	SymbolicExpression castToArrayElementReference(State state,
			SymbolicExpression pointer, CIVLSource source);

	/**
	 * Gets the symbolic universe used by this symbolic analyzer.
	 * 
	 * @return the symbolic universe
	 */
	SymbolicUniverse getUniverse();
}
