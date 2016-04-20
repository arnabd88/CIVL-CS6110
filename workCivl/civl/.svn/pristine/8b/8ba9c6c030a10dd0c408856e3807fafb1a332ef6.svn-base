/**
 * 
 */
package edu.udel.cis.vsl.civl.state.IF;

import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

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
	 * @param collectProcesses
	 *            shall processes be collected?
	 * @param collectScopes
	 *            shall scopes be collected?
	 * @param collectHeaps
	 *            shall heaps be collected?
	 * 
	 * @return the canonical version of the given state
	 */
	State canonic(State state, boolean collectProcesses, boolean collectScopes,
			boolean collectHeaps) throws CIVLHeapException;

	/**
	 * Returns the canonic, initial state for a CIVL Model.
	 * 
	 * @return the initial state
	 */
	State initialState(Model model) throws CIVLHeapException;

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
	 *            The PID of the process containing the variable
	 * @param value
	 *            The new value to be assigned to the variable
	 * @return A new state that is the old state modified by updating the value
	 *         of the variable
	 */
	State setVariable(State state, Variable variable, int pid,
			SymbolicExpression value);

	/**
	 * <p>
	 * Updates the value assigned to a variable in the state. Specifically,
	 * returns a state which is equivalent to the given one, except that the
	 * value assigned to the specified variable is replaced by the given value.
	 * </p>
	 * <p>
	 * In this version of the method, the variable is specified by its dynamic
	 * scope ID and variable ID.
	 * </p>
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
	 * <p>
	 * Adds a new process. The new process is created and one entry is pushed
	 * onto its call stack. That entry will have a dynamic scope whose parent is
	 * determined by the calling process (the process that is executing the
	 * spawn command to create this new process) and the given function. The
	 * parent dynamic scope is computed by starting with the current dynamic
	 * scope of the caller, and working up the parent chain, stopping at the
	 * first dynamic scope whose static scope matches the containing scope of
	 * the function. If no such dynamic scope is found in the chain, an
	 * IllegalArgumentException is thrown. Hence the calling process must have a
	 * non-empty call stack.
	 * </p>
	 * <p>
	 * The PID of the new process will be {@link State#numProcs()}, where state
	 * is the pre-state (the given state), not the new state.
	 * </p>
	 * 
	 * @param state
	 *            The old state.
	 * @param function
	 *            The function in which the new process starts.
	 * @param arguments
	 *            The arguments to this function call.
	 * @param callerPid
	 *            the PID of the process that is creating the new process
	 * @return A new state that is the old state modified by adding a process
	 *         whose location is the start location of the function and with a
	 *         new dynamic scope corresponding to the outermost lexical scope of
	 *         the function.
	 */
	State addProcess(State state, CIVLFunction function,
			SymbolicExpression[] arguments, int callerPid);

	/**
	 * <p>
	 * Adds a new process. The new process is created and one entry is pushed
	 * onto its call stack. That entry will have a dynamic scope whose parent is
	 * determined by the calling process (the process that is executing the
	 * spawn command to create this new process) and the given function. The
	 * parent dynamic scope is computed by starting with the current dynamic
	 * scope of the caller, and working up the parent chain, stopping at the
	 * first dynamic scope whose static scope matches the containing scope of
	 * the function. If no such dynamic scope is found in the chain, an
	 * IllegalArgumentException is thrown. Hence the calling process must have a
	 * non-empty call stack.
	 * </p>
	 * <p>
	 * The PID of the new process will be {@link State#numProcs()}, where state
	 * is the pre-state (the given state), not the new state.
	 * </p>
	 * 
	 * @param state
	 *            The old state.
	 * @param function
	 *            The function in which the new process starts.
	 * @param functionParentDyscope
	 *            The dyscope ID of the parent of the new function
	 * @param arguments
	 *            The arguments to this function call.
	 * @param callerPid
	 *            the PID of the process that is creating the new process
	 * @return A new state that is the old state modified by adding a process
	 *         whose location is the start location of the function and with a
	 *         new dynamic scope corresponding to the outermost lexical scope of
	 *         the function.
	 */
	State addProcess(State state, CIVLFunction function,
			int functionParentDyscope, SymbolicExpression[] arguments,
			int callerPid);

	/**
	 * Sets the process state for the designated process to be the process state
	 * with the empty stack.
	 * 
	 * @param state
	 *            the old state
	 * @param pid
	 *            the PID of the process to terminate
	 * @return state that is identical to old except that the process state for
	 *         process PID has been set to the process state with the empty
	 *         stack
	 */
	State terminateProcess(State state, int pid);

	/**
	 * Removes a process from the state. The process state associated to that
	 * process is set to null. No other part of the state is affected. To really
	 * get rid of the process state you need to call {@link #collectProcesses}.
	 * 
	 * @param state
	 *            The old state
	 * @param pid
	 *            The PID
	 * @return A new state that is the same as the old state with the process
	 *         state set to null
	 */
	State removeProcess(State state, int pid);

	/**
	 * Sets the location of a process. This changes the top stack frame for the
	 * process so that it points to the new location. The given process must
	 * have a non-empty stack (although the location component of that frame is
	 * not used, so it is OK if it is null). There is no change of the access of
	 * variables from the current location to the target location.
	 * 
	 * This may involve adding and removing scopes, if the scope of the new
	 * location differs from the original scope.
	 * 
	 * @param state
	 *            The old state.
	 * @param pid
	 *            The PID of the process making the move.
	 * @param location
	 *            The target location.
	 * @return A new state that is the same as the old state with the given
	 *         process at a new location, and scopes added and removed as
	 *         necessary
	 */
	State setLocation(State state, int pid, Location location);

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
	 *            The PID of the process making the move.
	 * @param location
	 *            The target location.
	 * @param accessChanged
	 *            True iff there is change of variable accessing (write or
	 *            read-only) from the current location to the target location
	 * @return A new state that is the same as the old state with the given
	 *         process at a new location, and scopes added and removed as
	 *         necessary
	 */
	State setLocation(State state, int pid, Location location,
			boolean accessChanged);

	/**
	 * Pushes a new entry onto the call stack for a process. Used when a process
	 * calls a function. The process should already exist and have a non-empty
	 * call stack.
	 * 
	 * @param state
	 *            The old state
	 * @param pid
	 *            The PID of the process making the call
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
	 * Pushes a new entry onto the call stack for a process. Used when a process
	 * calls a function. The process should already exist and have a non-empty
	 * call stack.
	 * 
	 * @param state
	 *            The old state
	 * @param pid
	 *            The PID of the process making the call
	 * @param function
	 *            The function being called
	 * @param functionParentDyscope
	 *            The dyscope ID of the parent of the new function
	 * @param arguments
	 *            The (actual) arguments to the function being called
	 * @return A new state that is the same as the old state with the given
	 *         process having a new entry on its call stack.
	 */
	State pushCallStack(State state, int pid, CIVLFunction function,
			int functionParentDyscope, SymbolicExpression[] arguments);

	/**
	 * Pops an entry off the call stack for a process. Does not modify or remove
	 * and dynamic scopes (even if they become unreachable). Does not nullify or
	 * remove the process state (even if the call stack becomes empty).
	 * 
	 * @param state
	 *            The old state.
	 * @param pid
	 *            The PID of the process returning from a call.
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
	 * Performs a garbage collection and canonicalization of heaps.
	 * 
	 * Computes the set of reachable heap objects, and removes all unreachable
	 * heap objects. Renumbers heap objects in a canonic way. Updates all
	 * pointers in the state accordingly. This operation should be completely
	 * invisible to the user.
	 * 
	 * @param state
	 *            a state
	 * @return the state after canonicalizing heaps, which may be this state or
	 *         a new one
	 */
	State collectHeaps(State state) throws CIVLStateException;

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
	State collectScopes(State state) throws CIVLStateException;

	/**
	 * Performs a garbage collection and canonicalization of the process states.
	 * Removes any process state that is null. Renumbers the PIDs so that there
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
	 * This information is maintained as a global variable of <code>$proc</code>
	 * type in the root scope in the CIVL model (always with index 0), and it
	 * gets automatically updated when process id's are renumbered.
	 * </p>
	 * 
	 * @param state
	 *            The state to be checked
	 * @return True iff the value of the variable atomic lock is not undefined.
	 */
	boolean lockedByAtomic(State state);

	/**
	 * Returns the PID of the process that holds the atomic lock at a certain
	 * state
	 * 
	 * @param state
	 *            The state to be checked
	 * @return -1 iff there is no process holding the atomic lock, otherwise
	 *         return the process that holds the atomic lock
	 */
	int processInAtomic(State state);

	/**
	 * Declares that the process with the given PID now owns the atomic lock.
	 * Precondition: no process is holding the atomic lock in the given state.
	 * 
	 * @param state
	 *            any non-null CIVL state
	 * @param pid
	 *            The PID of the process that is going to take the atomic lock
	 * @return a state equivalent to given one except that process PID now owns
	 *         the atomic lock
	 */
	State getAtomicLock(State state, int pid);

	/**
	 * Releases the atomic lock, by updating the atomic lock variable with the
	 * undefined process value. If atomic lock of the given state is already
	 * released, this is a no op.
	 * 
	 * @param state
	 *            any non-null CIVL state
	 * @return a state equivalent to given one except that no state owns the
	 *         atomic lock
	 */
	State releaseAtomicLock(State state);

	/**
	 * <p>
	 * Updates the state by replacing the process state with the given one where
	 * the PID of the old process state is the same as the given process state.
	 * </p>
	 * <p>
	 * Precondition: the PID of the given process state should be in [0,
	 * numProcs-1].
	 * </p>
	 * 
	 * @param state
	 *            A non-null CIVL state
	 * @param processState
	 *            The process state to assign to PID
	 * @return The new state after updating the process with the specified PID
	 */
	State setProcessState(State state, ProcessState processState);

	/**
	 * Checks if one dyscope is strictly the descendant of the other (not equal
	 * to).
	 * 
	 * @param state
	 *            The current state.
	 * @param ancestor
	 *            The ID of the ancestor dyscope.
	 * @param descendant
	 *            The ID of the descendant dyscope.
	 * @return True iff ancestor dyscope is really an ancestor of the descendant
	 *         dyscope and they must not be equal to each other.
	 */
	boolean isDescendantOf(State state, int ancestor, int descendant);

	/**
	 * Computes the lowest common ancestor of two given dyscopes. The returned
	 * value is always a dyscope ID.
	 * 
	 * @param state
	 *            The current state.
	 * @param one
	 *            One dyscope.
	 * @param another
	 *            Another dynamic scope.
	 * @return The dyscope ID of the lowest common ancestor of the two given
	 *         dyscopes.
	 */
	int lowestCommonAncestor(State state, int one, int another);

	/**
	 * Allocates an object, of the given value, for the given malloc ID in the
	 * heap of the given dyscope. For handle objects that are allocated by
	 * system functions instead of malloc statement, they all have a
	 * corresponding fake malloc ID assigned by the model builder.
	 * 
	 * @param state
	 *            The pre-state.
	 * @param dyscopeID
	 *            The dyscope ID.
	 * @param mallocID
	 *            The ID the malloc statement.
	 * @param heapObject
	 *            The value of the new heap object.
	 * @return The new state after the new heap object
	 */
	Pair<State, SymbolicExpression> malloc(State state, int dyscopeID,
			int mallocID, SymbolicExpression heapObject);

	/**
	 * Allocates an object for the given malloc ID in the heap of the given
	 * dyscope. For handle objects that are allocated by system functions
	 * instead of malloc statement, they all have a corresponding fake malloc ID
	 * assigned by the model builder. Since no value of the heap object is
	 * provided, the method will create a symbolic constant representing the
	 * heap object.
	 * 
	 * @param state
	 *            The pre-state.
	 * @param pid
	 *            The PID of the process that triggers this execution.
	 * @param dyscopeID
	 *            The dyscope ID.
	 * @param mallocID
	 *            The ID the malloc statement.
	 * @param elementType
	 *            The symbolic type of the element to be contained in the new
	 *            heap object.
	 * @param elementCount
	 *            The number of elements contained by the new heap object.
	 * @return The new state after the new heap object is added.
	 */
	Pair<State, SymbolicExpression> malloc(State state, int pid, int dyscopeID,
			int mallocID, SymbolicType elementType,
			NumericExpression elementCount);

	/**
	 * Deallocates a heap object from the heap of a given dyscope. It marks the
	 * heap object as INVALID instead of removing it, updates any pointer to
	 * that removed object to be an UNDEFINED pointer, which is defined by the
	 * symbolic utility. The removal of the heap object happens later when the
	 * heap gets collected during state canonicalization.
	 * 
	 * @see malloc
	 * 
	 * @param state
	 *            The pre-state.
	 * @param heapObjectPointer
	 *            The pointer which points to the heap object to be removed.
	 * @param dyscopeId
	 *            The ID of the dyscope where the pointer points to.
	 * @param mallocId
	 *            The malloc ID of the heap object to be removed, i.e., the
	 *            index of the heap field in the heap.
	 * @param index
	 *            The index of the heap object in the heap field.
	 * @return A new state after the heap object is removed from the heap, and
	 *         corresponding pointers updated.
	 */
	State deallocate(State state, SymbolicExpression heapObjectPointer,
			int dyscopeId, int mallocId, int index);

	/**
	 * Increase the number of symbolic constants by one.
	 * 
	 * @param state
	 *            the state whole number of symbolic constants is to be
	 *            increased.
	 * @return the new state
	 */
	State incrementNumSymbolicConstants(State state);

	/**
	 * Returns the number of symbolic constants appearing in the given state.
	 * 
	 * @param state
	 *            the given state
	 * @return the number of symbolic constants appearing in the given state.
	 */
	int numSymbolicConstants(State state);

	MemoryUnitFactory memUnitFactory();
}
