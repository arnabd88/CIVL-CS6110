/**
 * 
 */
package edu.udel.cis.vsl.civl.state.IF;

import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * The state factory is used to create all state objects.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * @author Timothy J. McClory (tmcclory)
 * @author Stephen F. Siegel (siegel)
 * 
 */
public interface StateFactory {

	/**
	 * Returns the symbolic universe used by this factory to manipulate symbolic
	 * expressions.
	 * 
	 * @return the symbolic universe
	 */
	SymbolicUniverse symbolicUniverse();

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
	 * Creates the canonic, initial state for a CIVL Model.
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
	 * @param vid
	 *            variable ID number
	 * @param scopeID
	 *            The ID of the dynamic scope containing the variable. This
	 *            version of the method is useful when setting the target of a
	 *            pointer. For a variable in the current lexical scope, use the
	 *            version of the method without this argument.
	 * @param value
	 *            The new value of the dynamic variable.
	 * @return A new state that is the old state modified by updating the value
	 *         of the variable.
	 */
	State setVariable(State state, int vid, int scopeId,
			SymbolicExpression value);

	/**
	 * Add a new process. The new process is created and one entry is pushed
	 * onto its call stack. That entry will have a dynamic scope whose parent is
	 * determined by the calling process (the process that is executing the
	 * spawn command to create this new process) and the given function. The
	 * parent dynamic scope is computed by starting with the current dynamic
	 * scope of the caller, and working up the parent chain, stopping at the
	 * first dynamic scope whose static scope matches the containing scope of
	 * the function. If no such dyanmic scope is found in the chain, an
	 * IllegalArgumentException is thrown. Hence the calling process must have a
	 * non-empty call stack.
	 * 
	 * The PID of the new process will be state.numProcs(), where state is the
	 * pre-state (the given state), not the new state.
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
	State addProcess(State state, CIVLFunction function,
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
	State pushCallStack(State state, int pid, CIVLFunction function,
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
	 * Simplies all variable values in the state, using the path condition as
	 * the simplification context.
	 * 
	 * @param state
	 *            The old state.
	 * @return The simplified state
	 */
	State simplify(State state);

	/**
	 * Returns the number of objects of type State that have been instantiated
	 * since this JVM started.
	 * 
	 * @return the number of states instantiated
	 */
	long getNumStateInstances();

	/**
	 * Returns the number of states saved, i.e., made canonic.
	 * 
	 * @return the number of canonic states
	 */
	int getNumStatesSaved();

	/**
	 * Performs a garbage collection and canonicalization of dynamic scopes.
	 * 
	 * Compute the set of reachable dynamic scopes, and removes any which are
	 * unreachable. Renumbers the dynamic scopes in a canonic way. Updates all
	 * scope references in the state. This operation should be completely
	 * invisible to the user.
	 * 
	 * @param state
	 *            a state
	 * @return the state after canonicalizing scopes, which may be this state or
	 *         a new one
	 */
	State collectScopes(State state);

	/**
	 * Check if any process at the state is holding the atomic lock, i.e, the
	 * process is executing some atomic blocks.
	 * <p>
	 * This information is maintained as a global variable
	 * {@link CommonModelFactory#ATOMIC_LOCK_VARIABLE} of $proc type in the root
	 * scope in the CIVL model (always with index 0), and it gets automatically
	 * updated when process id's are renumbered.
	 * 
	 * @param state
	 *            The state to be checked
	 * @return True iff the value of the variable $atomicLock is not undefined.
	 */
	boolean lockedByAtomic(State state);

	/**
	 * Get the process that holds the atomic lock at a certain state
	 * 
	 * @param state
	 *            The state to be checked
	 * @return NULL iff there is no process holding the atomic lock, otherwise
	 *         return the process that holds the atomic lock
	 */
	ProcessState processInAtomic(State state);

	/**
	 * Process with pid grabs the atomic lock
	 * 
	 * @param state
	 *            The state to be worked on
	 * @param pid
	 *            The id of the process that is going to grab the atomic lock
	 * @return
	 */
	State getAtomicLock(State state, int pid);

	/**
	 * Release the atomic lock, by updating the atomic lock variable with the
	 * undefined process value
	 * 
	 * @param state
	 *            The state to be worked on
	 * @return
	 */
	State releaseAtomicLock(State state);

	/**
	 * Update a particular process of a certain state by process id.
	 * <p>
	 * Precondition: <code>p.pid() == pid</code>.
	 * 
	 * @param state
	 *            The state to be worked on
	 * @param p
	 *            The new process that is to be used to update the state
	 * @param pid
	 *            The process id of the process to be updated.
	 * @return The new state after updating the process with the specified id
	 */
	State setProcessState(State state, ProcessState p, int pid);
}
