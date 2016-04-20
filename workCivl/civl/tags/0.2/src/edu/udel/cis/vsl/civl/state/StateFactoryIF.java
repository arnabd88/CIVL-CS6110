/**
 * 
 */
package edu.udel.cis.vsl.civl.state;

import edu.udel.cis.vsl.civl.model.IF.Function;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * The state factory is used to create all state objects.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * @author Timothy J. McClory (tmcclory)
 * 
 */
public interface StateFactoryIF {

	/**
	 * Return a "canonical" version of the given state. This relates to the
	 * Flyweight Pattern. The state factory maintains a set consisting of one
	 * canonical representative of each equivalence class of states.
	 * (Equivalence is defined by the equals relation on State.) This method
	 * will return the representative from the class containing the given state.
	 * If this factory does not already posses a canonical state equivalent to
	 * the given state, it will make the given state the canonical
	 * representative. The canonical representatives also have a unique stateId
	 * field.
	 * 
	 * @param state
	 * @return the canonical representative of the given state
	 */
	State canonic(State state);

	/**
	 * Creates the canonic, initial state for a Chapel Model.
	 * 
	 * @return the initial state
	 */
	State initialState(Model model);

	/**
	 * Update the value of a dynamic variable in the state.
	 * 
	 * @param state
	 *            The old state.
	 * @param variable
	 *            The dynamic variable to update.
	 * @param pid
	 *            The pid of the process containing the variable.
	 * @param value
	 *            The new value of the dynamic variable.
	 * @return A new state that is the old state modified by updating the value
	 *         of the variable.
	 */
	State setVariable(State state, Variable variable, int pid,
			SymbolicExpression value);

	/**
	 * Update the value of a dynamic variable in the state.
	 * 
	 * @param state
	 *            The old state.
	 * @param variable
	 *            The dynamic variable to update.
	 * @param scopeID
	 *            The ID of the scope containing the variable. This version of
	 *            the method is useful when setting the target of a pointer. For
	 *            a variable in the current lexical scope, use the version of
	 *            the method without this argument.
	 * @param pid
	 *            The pid of the process containing the variable.
	 * @param value
	 *            The new value of the dynamic variable.
	 * @return A new state that is the old state modified by updating the value
	 *         of the variable.
	 */
	State setVariable(State state, Variable variable, int scopeId, int pid,
			SymbolicExpression value);

	/**
	 * Add a new process. The new process is created and one entry is pushed
	 * onto its call stack. That entry will have a dynamic scope whose parent is
	 * determined by the calling process (the process that is executing the fork
	 * command to create this new process) and the given function. The parent
	 * dynamic scope is computed by starting with the current dynamic scope of
	 * the caller, and working up the parent chain, stopping at the first
	 * dynamic scope whose static scope matches the containing scope of the
	 * function. If no such dyanmic scope is found in the chain, an
	 * IllegalArgumentException is thrown. Hence the calling process must have a
	 * non-empty call stack.
	 * 
	 * @param state
	 *            The old state.
	 * @param function
	 *            The function in which the new process starts.
	 * @param arguments
	 *            The arguments to this function call.
	 * @param callerPid
	 *            the pid of the process that is creating the new process
	 * 
	 * @return A new state that is the old state modified by adding a process
	 *         whose location is the start location of the function and with a
	 *         new dynamic scope corresponding to the outermost lexical scope of
	 *         the function.
	 */
	State addProcess(State state, Function function,
			SymbolicExpression[] arguments, int callerPid);

	/**
	 * Removes a process from the state. Re-numbers the PIDs to remove the gap
	 * in the PID sequence, updating any process reference value occurring in
	 * the state. Removes any scopes that become unreachable and re-numbers the
	 * scopes in a canonical order.
	 * 
	 * @param state
	 *            The old state.
	 * @param pid
	 *            The process ID.
	 * @return A new state that is the same as the old state with the process
	 *         removed.
	 */
	State removeProcess(State state, int pid);

	/**
	 * Sets the location of a process. This changes the top stack frame for the
	 * process so that it points to the new location. The given process must
	 * have a non-empty stack (although the location component of that frame is
	 * not used, so it is OK if it is null).
	 * 
	 * This may involve adding and removing scopes, if the scope of the new
	 * location differs from the original scope.
	 * 
	 * @param state
	 *            The old state.
	 * @param pid
	 *            The pid of the process making the move.
	 * @param location
	 *            The target location.
	 * @return A new state that is the same as the old state with the given
	 *         process at a new location, and scopes added and removed as
	 *         necessary
	 */
	State setLocation(State state, int pid, Location location);

	/**
	 * Push a new entry on the call stack for a process. Used when a process
	 * calls a function. The process should already exist and have a non-empty
	 * call stack.
	 * 
	 * @param state
	 *            The old state.
	 * @param pid
	 *            The pid of the process making the call.
	 * @param location
	 *            The location of the function in the new stack frame.
	 * @param parentScopeId
	 *            The id of the parent dynamic scope.
	 * @return A new state that is the same as the old state with the given
	 *         process having a new entry on its call stack.
	 */
	State pushCallStack(State state, int pid, Function function,
			SymbolicExpression[] arguments);

	/**
	 * Pop an entry off the call stack for a process. Removes scopes that become
	 * unreachable. Does NOT remove the process from the state (even if the
	 * stack becomes empty).
	 * 
	 * @param state
	 *            The old state.
	 * @param pid
	 *            The pid of the process returning from a call.
	 * @return A new state that is the same as the old state but with the call
	 *         stack for the given process popped.
	 */
	State popCallStack(State state, int pid);

	/**
	 * Update the path condition of a state.
	 * 
	 * @param state
	 *            The old state.
	 * @param pathCondition
	 *            The new path condition.
	 * @return A new state that is the same as the old state but with the new
	 *         path condition.
	 */
	State setPathCondition(State state, SymbolicExpression pathCondition);

}
