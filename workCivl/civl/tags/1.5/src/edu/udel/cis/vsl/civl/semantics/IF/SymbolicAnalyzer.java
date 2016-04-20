package edu.udel.cis.vsl.civl.semantics.IF;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
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
	StringBuffer stateInformation(State state);

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
			CIVLType type, SymbolicExpression symbolicExpression);

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
	 * pre-condition:
	 * <ol>
	 * <li>"arrayPtr" must point to an array</li>
	 * <li>"source" is the @{link CIVLSource} of the pointer expression</li>
	 * </ol>
	 * post-condition:
	 * <ol>
	 * <li>the returned {@link CIVLType} must not be an array type</li>
	 * <li>the returned object cannot be null</li>
	 * </ol>
	 * Get the type of the non-array element of an array by given a pointer to
	 * an array
	 * 
	 * @param array
	 * @return the type of the non-array element of an array
	 */
	CIVLType getArrayBaseType(State state, CIVLSource source,
			SymbolicExpression arrayPtr);

	/**
	 * 
	 * pre-condition:
	 * <ol>
	 * <li>"source" is the @{link CIVLSource} of the pointer expression</li>
	 * </ol>
	 * post-condition:
	 * <ol>
	 * <li>the returned object cannot be null</li>
	 * </ol>
	 * Returns the {@link ReferenceExpression} directly to the object which has
	 * the physical base type of the pointed array (or object) residing in
	 * memory. <br>
	 * Note: The "physical base type" means the base type of the a physical
	 * sequence of objects in memory space. For example: <code> 
	 * int ** a; 
	 * int b[2][2];
	 * int c;
	 * 
	 * a = (int **)malloc(..);
	 * </code> The "physical base type" of "a" is "int *" while both of "b" and
	 * of "c" is "int".
	 * 
	 * 
	 * @author Ziqing Luo
	 * @param state
	 *            The current state
	 * @param process
	 *            The information of the process
	 * @param source
	 *            The CIVL source of the pointer
	 * @return The Reference to the object that has physical base type
	 * @throws UnsatisfiablePathConditionException
	 */
	ReferenceExpression getMemBaseReference(State state,
			SymbolicExpression pointer, CIVLSource source);

	/**
	 * Gets the symbolic universe used by this symbolic analyzer.
	 * 
	 * @return the symbolic universe
	 */
	SymbolicUniverse getUniverse();

	/**
	 * Compute a friendly string representation of an expression's evaluation.
	 * Eg, if the expression is a+b, then return 8+9 supposing a=8, b=9.
	 * 
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	Pair<State, String> expressionEvaluation(State state, int pid,
			Expression expression, boolean resultOnly)
			throws UnsatisfiablePathConditionException;

	StringBuffer statementEvaluation(State preState, State postState, int pid,
			Statement statement) throws UnsatisfiablePathConditionException;

	StringBuffer inputVariablesToStringBuffer(State state);

	Evaluator evaluator();
	
	SymbolicExpression pointerArithmetics(CIVLSource source,
			State state, boolean isSubtract, SymbolicExpression pointer,
			SymbolicExpression offset) ;
}
