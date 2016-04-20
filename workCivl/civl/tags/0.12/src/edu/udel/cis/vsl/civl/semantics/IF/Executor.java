package edu.udel.cis.vsl.civl.semantics.IF;

import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

public interface Executor {

	/**
	 * Assigns a value to the referenced cell in the state. Returns a new state
	 * which is equivalent to the old state except that the memory specified by
	 * the given pointer value is assigned the given value.
	 * 
	 * @param state
	 *            a CIVL model state
	 * @param pointer
	 *            a pointer value
	 * @param value
	 *            a value to be assigned to the referenced memory location
	 * @return the new state
	 * @throws UnsatisfiablePathConditionException
	 */
	State assign(CIVLSource source, State state, String process,
			SymbolicExpression pointer, SymbolicExpression value)
			throws UnsatisfiablePathConditionException;

	/**
	 * Assigns a value to the memory location specified by the given
	 * left-hand-side expression.
	 * 
	 * @param state
	 *            a CIVL model state
	 * @param pid
	 *            the PID of the process executing the assignment
	 * @param lhs
	 *            a left-hand-side expression
	 * @param value
	 *            the value being assigned to the left-hand-side
	 * @return the new state
	 * @throws UnsatisfiablePathConditionException
	 */
	State assign(State state, int pid, String process, LHSExpression lhs,
			SymbolicExpression value)
			throws UnsatisfiablePathConditionException;

	/**
	 * @return The state factory associated with this executor.
	 */
	StateFactory stateFactory();

	/**
	 * @return The evaluator used by this executor.
	 */
	Evaluator evaluator();

	/**
	 * Returns the number of "steps" executed since this Executor was created.
	 * 
	 * @return the number of steps executed
	 */
	long getNumSteps();

	/**
	 * Adds a new object to the heap of a certain scope; sets the pointer of the
	 * object in the heap to the provided left-hand-side expression (or does
	 * nothing if no left-hand-side expression is specified).
	 * 
	 * @param source
	 *            The source code element to be used to report errors.
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the process where this computation happens.
	 * @param lhs
	 *            The left-hand-side expression to store the pointer to the
	 *            added object.
	 * @param scopeExpression
	 *            The static expression of the scope value.
	 * @param scopeValue
	 *            The symbolic expression of the scope.
	 * @param objectType
	 *            The CIVL type of the object to be added, needed to decide the
	 *            field index in the heap.
	 * @param objectValue
	 *            The object to be added to the heap.
	 * @return The new state after adding the given object to the heap in the
	 *         given scope.
	 * @throws UnsatisfiablePathConditionException
	 */
	State malloc(CIVLSource source, State state, int pid, String process,
			LHSExpression lhs, Expression scopeExpression,
			SymbolicExpression scopeValue, CIVLType objectType,
			SymbolicExpression objectValue)
			throws UnsatisfiablePathConditionException;

	/**
	 * Returns the state that results from executing the statement, or null if
	 * path condition becomes unsatisfiable.
	 * 
	 * @param state
	 * @param pid
	 * @param transition
	 * @return
	 */
	State execute(State state, int pid, Transition transition)
			throws UnsatisfiablePathConditionException;

	/**
	 * Returns the error logger used by this executor.
	 * 
	 * @return The error logger used by this executor.
	 */
	CIVLErrorLogger errorLogger();
}
