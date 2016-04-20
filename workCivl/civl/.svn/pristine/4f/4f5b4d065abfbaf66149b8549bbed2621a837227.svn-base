package edu.udel.cis.vsl.civl.semantics.IF;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.civl.util.IF.Triple;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * This is the CIVL main evaluator. First, it is responsible for evaluating all
 * expressions. Second, it also provides some utility methods to be used by
 * library executor/evaluator/enabler, like the methods related to heap. Third,
 * it implements helper methods for the partial order reduction in pointer
 * reachability analysis. TODO: does it have state?
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public interface Evaluator {

	/**
	 * Given a pointer value, dereferences it in the given state to yield the
	 * symbolic expression value stored at the referenced location.
	 * 
	 * @param source
	 *            Source code information for error report.
	 * @param state
	 *            The state where the operation happens.
	 * @param process
	 *            The process information (name, PID) for error report.
	 * @param pointer
	 *            A pointer value which refers to some sub-structure in the
	 *            state, and is to dereferenced.
	 * @param checkedOutput
	 *            If this dereference operation is to read the variable (opposed
	 *            to write).
	 * @return the value pointed to
	 * @throws UnsatisfiablePathConditionException
	 */
	Evaluation dereference(CIVLSource source, State state, String process,
			SymbolicExpression pointer, boolean checkedOutput)
			throws UnsatisfiablePathConditionException;

	/**
	 * Returns the error logger object of this evaluator.
	 * 
	 * @return The error logger object of this evaluator.
	 */
	CIVLErrorLogger errorLogger();

	/**
	 * Evaluates the expression and returns the result, which is a symbolic
	 * expression value.
	 * 
	 * If a potential error is encountered while evaluating the expression (e.g.
	 * possible division by 0 in x/y), the error is logged, a correcting side
	 * effect (e.g. y!=0) is added to the path condition, and execution
	 * continues. It is possible for the side effect to make the path condition
	 * unsatisfiable. When this happens, an UnsatisfiablePathConditionException
	 * is thrown.
	 * 
	 * @param state
	 *            the state in which the evaluation takes place
	 * @param pid
	 *            the PID of the process which is evaluating the expression
	 * @param expression
	 *            the (static) expression being evaluated
	 * @return the result of the evaluation
	 * @throws UnsatisfiablePathConditionException
	 *             if a side effect that results from evaluating the expression
	 *             causes the path condition to become unsatisfiable
	 */
	Evaluation evaluate(State state, int pid, Expression expression)
			throws UnsatisfiablePathConditionException;

	/**
	 * Evaluates a function pointer expression. TODO: add ID for functions in
	 * the model. TODO: get rid of this function by adding a helper function to
	 * extract a function from a function pointer value. No need to have special
	 * handling for function pointer: can treat it like ordinary pointers.
	 * 
	 * @param state
	 *            The state where the evaluation happens.
	 * @param pid
	 *            The PID of the process that triggers this evaluation.
	 * @param functionPointer
	 *            The function pointer expression to be evaluated.
	 * @param source
	 *            The source code information for error report
	 * @return The new state after the evaluation with possible side effect, the
	 *         function that the function pointer points to, and the dyscope ID
	 *         of the function that the given function pointer refers to.
	 * @throws UnsatisfiablePathConditionException
	 */
	Triple<State, CIVLFunction, Integer> evaluateFunctionPointer(State state,
			int pid, Expression functionPointer, CIVLSource source)
			throws UnsatisfiablePathConditionException;

	Evaluation initialValueOfStateVariable(CIVLSource source, State state,
			int pid, CIVLType type) throws UnsatisfiablePathConditionException;

	/**
	 * Evaluate the size of a CIVL type.
	 * 
	 * TODO is this necessarily public?
	 * 
	 * @param source
	 *            The source code element to be used for error report.
	 * @param state
	 *            The state where the evaluation happens.
	 * @param pid
	 *            The ID of the process that triggers the evaluation.
	 * @param type
	 *            The CIVL type whose size is to be evaluated.
	 * @return the result of the evaluation, including the symbolic expression
	 *         of the size of the type and a state
	 * @throws UnsatisfiablePathConditionException
	 */
	Evaluation evaluateSizeofType(CIVLSource source, State state, int pid,
			CIVLType type) throws UnsatisfiablePathConditionException;

	/**
	 * Given a pointer to char, returns the symbolic expression of type array of
	 * char which is the string pointed to.
	 * 
	 * The method will succeed if any of the following holds: (1) the pointer
	 * points to element 0 of an array of char. In that case, it is just assumed
	 * that the string is the whole array. (2) the pointer points to element i
	 * of an array of char, where i is a concrete positive integer and the array
	 * length is also concrete. In that case, the elements of the array are
	 * scanned starting from position i until the first null character is
	 * reached, or the end of the array is reached, and the string is
	 * constructed from those scanned characters (including the null character).
	 * In other situations, this method may fail, in which case it throws an
	 * exception.
	 * 
	 * @param state
	 *            the state in which this evaluation is taking place
	 * @param source
	 *            the source information used to report errors
	 * @param charPointer
	 *            a symbolic expression which is a pointer to a char
	 * @return the symbolic expression which is an array of type char
	 *         representing the string pointed to
	 * @throws UnsatisfiablePathConditionException
	 *             of something goes wrong evaluating the string
	 * @throws CIVLUnimplementedFeatureException
	 *             if it is not possible to extract the string expression.
	 */
	Evaluation getStringExpression(State state, String process,
			CIVLSource source, SymbolicExpression charPointer)
			throws UnsatisfiablePathConditionException;

	/**
	 * Computes the reachable memory units of an expression recursively and adds
	 * those memory units to the given set.
	 * 
	 * @param state
	 *            The state where the computation happens.
	 * @param pid
	 *            The ID of the process that the expression belongs to.
	 * @param expression
	 *            The expression whose impact memory units are to be computed.
	 * @param memoryUnits
	 *            The set of memory units reachable by the expression.
	 * @throws UnsatisfiablePathConditionException
	 */
	void memoryUnitsOfExpression(State state, int pid, Expression expression,
			Set<SymbolicExpression> memoryUnits)
			throws UnsatisfiablePathConditionException;

	/**
	 * <p>
	 * Compute reachable memory units by referencing a variable at a certain
	 * state. For example, given int x = 9; int* y = &x; int *z = y; Then the
	 * reachable memory units from z is {&z, &x}.
	 * </p>
	 * TODO: check if we can get rid of variableValue; add precondition if it is
	 * necessary for some reason.
	 * 
	 * 
	 * @param variableValue
	 *            The value of the variable.
	 * @param dyScopeID
	 *            The dynamic scope id of the variable.
	 * @param vid
	 *            The id of the variable in the scope.
	 * @param state
	 *            The state where the computation happens.
	 * @return The set of memory units that reachable from the given variable.
	 *         Every member of the set is a pointer value, and is a pointer to a
	 *         memory unit.
	 */
	Set<SymbolicExpression> memoryUnitsReachableFromVariable(
			CIVLType variableType, SymbolicExpression variableValue,
			int dyScopeID, int vid, State state, String process);

	/**
	 * The model factory should be the unique one used in the system.
	 * 
	 * @return The model factory of the evaluator.
	 */
	ModelFactory modelFactory();

	/**
	 * Evaluates pointer addition. Pointer addition involves the addition of a
	 * pointer expression and an integer. TODO: check if BinaryExpression
	 * expression is necessary.<br>
	 * Note: The given pointer for this function won't be casted to the deepest
	 * array element reference which is the only difference from the other
	 * function
	 * {@link #evaluatePointerAdd(State, String, SymbolicExpression, NumericExpresion, boolean, CIVLSource)}
	 * . <br>
	 * e.g. for <code>int a[2][2]</code>, passing pointer "a[0] + 1" will turn
	 * out a new pointer "a[1]".
	 * 
	 * @author Ziqing Luo
	 * 
	 * 
	 * @param state
	 *            the pre-state
	 * @param pid
	 *            the PID of the process evaluating the pointer addition
	 * @param expression
	 *            the pointer addition expression
	 * @param pointer
	 *            the result of evaluating argument 0 of expression
	 * @param offset
	 *            the result of evaluating argument 1 of expression
	 * @return the result of evaluating the sum of the pointer and the integer
	 * @throws UnsatisfiablePathConditionException
	 */
	Evaluation pointerAdd(State state, int pid, String process,
			BinaryExpression expression, SymbolicExpression pointer,
			NumericExpression offset)
			throws UnsatisfiablePathConditionException;

	/**
	 * Evaluation pointer subtraction. Pointer subtraction operation, a binary
	 * operation, whose two operands are both pointers to qualified or
	 * unqualified versions of compatible complete object types. Returns the
	 * difference of the two operands. Both pointers must point to elements of
	 * the same array or one past the last element of the same array.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The information of the process
	 * @param expression
	 *            The expression of the pointer subtraction statement
	 * @param leftPtr
	 *            The pointer at the left side of the minus operator
	 * @param rightPtr
	 *            The pointer at the right side of the minus operator
	 * 
	 * @return the difference of the subscripts of the two array elements
	 * @throws UnsatisfiablePathConditionException
	 */
	Evaluation pointerSubtraction(State state, int pid, String process,
			BinaryExpression expression, SymbolicExpression leftPtr,
			SymbolicExpression rightPtr)
			throws UnsatisfiablePathConditionException;

	/**
	 * Creates a pointer value by evaluating a left-hand-side expression in the
	 * given state.
	 * 
	 * @param state
	 *            a CIVL model state
	 * @param pid
	 *            the process ID of the process in which this evaluation is
	 *            taking place
	 * @param operand
	 *            the left hand side expression we are taking the address of
	 * @return the pointer value
	 * @throws UnsatisfiablePathConditionException
	 */
	Evaluation reference(State state, int pid, LHSExpression operand)
			throws UnsatisfiablePathConditionException;

	/**
	 * Returns the dynamic type pointed to by a pointer. Can be used even if the
	 * pointer can't be dereferenced (because it points off the end of an
	 * object, for example).
	 * 
	 * @param source
	 *            The source code element to be used in the error report.
	 * @param state
	 *            The state where the computation happens.
	 * @param pointer
	 *            The symbolic representation of the pointer whose type is to be
	 *            computed.
	 * @return The symbolic type that the given pointer is pointing to.
	 */
	SymbolicType referencedType(CIVLSource source, State state,
			SymbolicExpression pointer);

	/**
	 * The state factory should be the unique one used in the system.
	 * 
	 * @return The state factory of the evaluator.
	 */
	StateFactory stateFactory();

	/**
	 * Returns the symbolic utility object of this evaluator.
	 * 
	 * @return The symbolic utility object of this evaluator.
	 */
	SymbolicUtility symbolicUtility();

	/**
	 * The symbolic universe should be the unique one used in the system.
	 * 
	 * @return The symbolic universe of the evaluator.
	 */
	SymbolicUniverse universe();

	Pair<State, StringBuffer> getString(CIVLSource source, State state,
			String process, SymbolicExpression charPointer)
			throws UnsatisfiablePathConditionException;

	/**
	 * Do a pointer addition operation on the given pointer with the given
	 * offset. The given pointer will be casted to the deepest array element
	 * reference before the operation (e.g. for <code>int a[2][2];</code>, if
	 * giving pointer &a, it will be casted to &a[0][0]).
	 * 
	 * @param state
	 *            The current state
	 * @param process
	 *            The information of the process
	 * @param ptr
	 *            The pointer will be added by a offset
	 * @param offset
	 *            The numeric offset will be added to a pointer
	 * @param source
	 *            The CIVLSource of the statement.
	 * @return A pair of evaluation of the result of the operation and a map
	 *         contains the array elements sizes information of the array
	 *         pointed by the given pointer which helps saving computing time
	 *         for caller functions.
	 */
	public Pair<Evaluation, ArrayList<NumericExpression>> evaluatePointerAdd(
			State state, String process, SymbolicExpression ptr,
			NumericExpression offset, boolean ifCheckOutput, CIVLSource source)
			throws UnsatisfiablePathConditionException;

	List<ReferenceExpression> leafNodeReferencesOfType(CIVLSource source,
			State state, int pid, CIVLType type)
			throws UnsatisfiablePathConditionException;

	/**
	 * Evaluating the symbolic array type from a {@link CIVLArrayType} based on
	 * current state and specific process. This function supplements the
	 * built-in function {@link CIVLType#getDynamicType(SymbolicUniverse)} by
	 * providing the missing extent information.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param type
	 *            The CIVLArrayType object
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	public Pair<State, SymbolicArrayType> evaluateCIVLArrayType(State state,
			int pid, CIVLArrayType type)
			throws UnsatisfiablePathConditionException;
}
