/**
 * 
 */
package edu.udel.cis.vsl.civl.state.IF;

import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.model.common.CommonModelFactory;
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
	 * Return the "canonical" version of the given state.
	 * 
	 * The state returned will satisfy all of the following:
	 * <ul>
	 * <li>it will be observationally equivalent to the given state, i.e., there
	 * is no way a CIVL-C program can distinguish between the two states</li>
	 * <li>there will be no gaps in the dynamic scope IDs and no null dynamic
	 * scopes</li>
	 * <li>there will be no gaps in the PIDs and no null process states</li>
	 * <li>every dynamic scope will be reachable (starting from the frame of the
	 * call stack of one of the processes and following parent edges in the
	 * dyscope tree)
	 * <li>the state returned will be the unique representative of its
	 * equivalence class, i.e., if this method is invoked with two equivalent
	 * states, it will return the same object</li>
	 * </ul>
	 * 
	 * Note that the state returned may in fact be the same as the one given.
	 * 
	 * Note that this does everything that methods {@link #collectScopes(State)}
	 * and {@link #collectProcesses} do. So there is no need to call those
	 * methods if you are already calling this method.
	 * 
	 * This method may go further in simplifying the state. This is up to the
	 * particular implementation.
	 * 
	 * @param state
	 *            any non-null CIVL state
	 * @return the canonical version of the given state
	 */
	State canonic(State state);

	/**
	 * Returns the canonic, initial state for a CIVL Model.
	 * 
	 * @return the initial state
	 */
	State initialState(Model model);

	/**
	 * Updates the value assigned to a variable in the state. Specifically,
	 * returns a state which is equivalent to the given one, except that the
	 * value assigned to the specified variable is replaced by the given value.
	 * 
	 * @param state
	 *            The old state
	 * @param variable
	 *            The variable to update
	 * @param pid
	 *            The pid of the process containing the variable
	 * @param value
	 *            The new value to be assigned to the variable
	 * @return A new state that is the old state modified by updating the value
	 *         of the variable
	 */
	State setVariable(State state, Variable variable, int pid,
			SymbolicExpression value);

	/**
	 * Updates the value assigned to a variable in the state. Specifically,
	 * returns a state which is equivalent to the given one, except that the
	 * value assigned to the specified variable is replaced by the given value.
	 * 
	 * In this version of the method, the variable is specified by its dynamic
	 * scope ID and variable ID.
	 * 
	 * 
	 * @param state
	 *            The old state
	 * @param vid
	 *            variable ID number
	 * @param scopeID
	 *            The ID of the dynamic scope containing the variable. This
	 *            version of the method is useful when setting the target of a
	 *            pointer. For a variable in the current lexical scope, use the
	 *            version of the method without this argument
	 * @param value
	 *            The new value to assign to the variable
	 * @return A new state that is the old state modified by updating the value
	 *         of the variable
	 * @see #setVariable(State, Variable, int, SymbolicExpression)
	 */
	State setVariable(State state, int vid, int scopeId,
			SymbolicExpression value);

	/**
	 * Adds a new process. The new process is created and one entry is pushed
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
	 * Removes a process from the state. The process state associated to that
	 * process is set to null. No other part of the state is affected. To really
	 * get rid of the process state you need to call {@link #collectProcesses}.
	 * 
	 * @param state
	 *            The old state
	 * @param pid
	 *            The process ID
	 * @return A new state that is the same as the old state with the process
	 *         state set to null
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
	 * Pushes a new entry onto the call stack for a process. Used when a process
	 * calls a function. The process should already exist and have a non-empty
	 * call stack.
	 * 
	 * @param state
	 *            The old state
	 * @param pid
	 *            The pid of the process making the call
	 * @param function
	 *            The function being called
	 * @param arguments
	 *            The (actual) arguments to the function being called
	 * @return A new state that is the same as the old state with the given
	 *         process having a new entry on its call stack.
	 */
	State pushCallStack(State state, int pid, CIVLFunction function,
			SymbolicExpression[] arguments);

	/**
	 * Pops an entry off the call stack for a process. Does not modify or remove
	 * and dynamic scopes (even if they become unreachable). Does not nullify or
	 * remove the process state (even if the call stack becomes empty).
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
	 * Simplifies all variable values in the state, using the path condition as
	 * the simplification context. A symbolic constant which is determined to
	 * have a concrete value (based on the path condition), may be entirely
	 * removed from the state by replacing every occurrence of that symbol with
	 * the concrete value.
	 * 
	 * @param state
	 *            Any State
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
	 * Returns the number of states stored by this state factory.
	 * 
	 * @return the number of states stored
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
	 * Performs a garbage collection and canonicalization of the process states.
	 * Removes and process state that is null. Renumbers the PIDs so that there
	 * are no gaps (and start from 0).
	 * 
	 * @param state
	 *            any non-null CIVL state
	 * @return the state with processes collected
	 */
	State collectProcesses(State state);

	/**
	 * Checks if any process at the state is holding the atomic lock, i.e, the
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
	 * Returns the Id of the process that holds the atomic lock at a certain
	 * state
	 * 
	 * @param state
	 *            The state to be checked
	 * @return NULL iff there is no process holding the atomic lock, otherwise
	 *         return the process that holds the atomic lock
	 */
	int processInAtomic(State state);

	/**
	 * Declares that the process with the given pid now owns the atomic lock.
	 * 
	 * @param state
	 *            any non-null CIVL state
	 * @param pid
	 *            The pid of the process that is going to take the atomic lock
	 * @return a state equivalent to given one except that process pid now owns
	 *         the atomic lock
	 */
	State getAtomicLock(State state, int pid);

	/**
	 * Releases the atomic lock, by updating the atomic lock variable with the
	 * undefined process value.
	 * 
	 * @param state
	 *            any non-null CIVL state
	 * @return a state equivalent to given one except that no state owns the
	 *         atomic lock
	 */
	State releaseAtomicLock(State state);

	/**
	 * Sets the process state assigned to the given PID to the given
	 * ProcessState value.
	 * <p>
	 * Precondition: <code>p.pid() == pid</code>.
	 * 
	 * @param state
	 *            A non-null CIVL state
	 * @param processState
	 *            The process state to assign to PID
	 * @param pid
	 *            The process id of the process to be updated
	 * @return The new state after updating the process with the specified id
	 */
	State setProcessState(State state, ProcessState processState, int pid);

	/**
	 * Checks if one dyscope is strictly the descendant of the other (not equal
	 * to).
	 * 
	 * @param state
	 *            The current state.
	 * @param ancestor
	 *            The ID of the ancestor scope.
	 * @param descendant
	 *            The ID of the descendant scope.
	 * @return True iff ancestor scope is really an ancestor of the descendant
	 *         scope and they must not be equal to each other.
	 */
	boolean isDesendantOf(State state, int ancestor, int descendant);

	/**
	 * Computes the lowest common ancestor of two given scopes.
	 * 
	 * @param state
	 *            The current state.
	 * @param one
	 *            One dynamic scope.
	 * @param another
	 *            Another dynamic scope.
	 * @return The lowest common ancestor of the two given scopes.
	 */
	int lowestCommonAncestor(State state, int one, int another);
}
