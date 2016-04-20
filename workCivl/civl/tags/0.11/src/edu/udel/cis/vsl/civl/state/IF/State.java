package edu.udel.cis.vsl.civl.state.IF;

import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * A State represents the (global) state of a CIVL Model. It encodes:
 * 
 * <ul>
 * <li>a set of process states</li>
 * <li>a set of dynamic scopes</li>
 * <li>a path condition</li>
 * </ul>
 * 
 * The data listed above comprise the "intrinsic data" of the state. A State may
 * have additional "extrinsic data" but they should not affect the equals or
 * hashCode methods. Those methods should depend only on the three intrinsic
 * data listed above.
 * 
 * States may be mutable or immutable (or something in between). The contract
 * for the state modules does not specify this. However, states must supply a
 * "commit" method. After invoking this method, the state must be essentially
 * immutable, which means its intrinsic data (and therefore hash code) cannot
 * change.
 * 
 * 
 * The processes and dynamic scopes are ordered within any one State. However
 * their order may change from State to State.
 * 
 * In addition, States may participate in the Flyweight Pattern. We say two
 * states are equivalent if the <code>equals</code> method says they are equal.
 * (This means they have "equal" intrinsic data; the extrinsic data are
 * completely ignored.) The point of the Flyweight Pattern is to choose one
 * representative State from each equivalence class. This pattern is provided
 * through a method in the StateFactory, {@link StateFactory#canonic(State)}.
 * That method takes any State, and return the State which is the canonic
 * representative of the given State's equivalence class. The canonic State are
 * also given unique "canonic ID numbers".
 * 
 * 
 * @author Stephen F. Siegel (siegel)
 * @author Timothy K. Zirkel (zirkel)
 * @author Tim McClory (tmcclory)
 * 
 */
public interface State {

	/**
	 * The string of the form canonicId:instanceId. Used to easily identify this
	 * instance.
	 * 
	 * @return string canonicId:instanceId
	 */
	String identifier();

	/**
	 * Makes this state immutable (if it is not already).
	 */
	void commit();

	/**
	 * Returns the number of dynamic scopes in this state.
	 * 
	 * @return the number of dynamic scopes in this state
	 */
	int numScopes();

	/**
	 * Returns the number of process states in this state.
	 * 
	 * @return the number of process states in this state, including nulls.
	 */
	int numProcs();

	/**
	 * Returns the dynamic scope ID of the root (or "system") scope.
	 * 
	 * @return the root dynamic scope ID
	 */
	int rootScopeID();

	/**
	 * Returns the path condition.
	 * 
	 * @return the path condition.
	 */
	BooleanExpression getPathCondition();

	/**
	 * Has this state been seen before in the depth-first search? This is simply
	 * the "getter" for the "setter" method {@link #setSeen(boolean)}.
	 * 
	 * @return true iff this state has been seen before
	 */
	boolean seen();

	/**
	 * Is this state currently on the depth-frist search stack? This is simply
	 * the "getter" for the "setter" method {@link #setOnStack(boolean)}.
	 * 
	 * @return true iff this state is on the DFS stack
	 */
	boolean onStack();

	/**
	 * Sets the seen bit to the given value.
	 * 
	 * @param value
	 *            whether this state has been seen in the depth first search
	 */
	void setSeen(boolean value);

	/**
	 * Sets the "onStack" bit to the given value.
	 * 
	 * @param onStack
	 *            whether this state is on the DFS stack
	 */
	void setOnStack(boolean onStack);

	/**
	 * Gets the dynamic scope ID (dyscope ID) of the parent of the dynamic scope
	 * with the given dyscope ID. If the dynamic scope with the given ID is the
	 * root scope (which has no parent), the result is -1.
	 * 
	 * @param scopeId
	 *            a dynamic scope ID in the range [0,numScopes-1]
	 * @return dynamic scope ID of the parent of the dynamic scope specified by
	 *         scopeId
	 */
	int getParentId(int scopeId);

	int getScopeId(int pid, Variable variable);

	SymbolicExpression getVariableValue(int scopeId, int variableId);

	SymbolicExpression valueOf(int pid, Variable variable);

	// void print(PrintStream out);

	@Override
	String toString();

	/**
	 * Sets the "depth" field of this state to the given value. This is another
	 * field used by a depth-first search. It is used when searching for a
	 * minimal counterexample, i.e., a shortest path to a violating state.
	 * 
	 * @param value
	 *            an integer which is currently the least depth at which this
	 *            state has been encountered in the DFS
	 */
	void setDepth(int value);

	/**
	 * Returns the "depth" field for this state. This is another field used by a
	 * depth-first search. It is used when searching for a minimal
	 * counterexample, i.e., a shortest path to a violating state.
	 * 
	 * @return an integer which is currently the least depth at which this state
	 *         has been encountered in the DFS
	 */
	int getDepth();

	/**
	 * Returns the process state for the pid-th process. The process state
	 * encodes the state of the call stack for the process.
	 * 
	 * The processes in this state are numbered with consecutive integers
	 * starting from 0. This number is the PID.
	 * 
	 * @param pid
	 *            the process ID
	 * @return the process state
	 */
	ProcessState getProcessState(int pid);

	/**
	 * Returns the id-th dynamic scope in this state. The dynamic scopes are
	 * numbered starting from 0.
	 * 
	 * The dynamic scope specifies a value (a symbolic expression) for each
	 * variable occurring in the static scope of which the dynamic scope is an
	 * instance.
	 * 
	 * @param id
	 *            the dyscope ID, an integer in the range [0,numScopes-1]
	 * @return the dynamic scope with that ID
	 */
	DynamicScope getScope(int id);

	int getDyScope(int pid, Scope scope);

	/**
	 * Returns the set of process states as an Iterable. This should not be
	 * modified. It is convenient when you want to iterate over the states,
	 * e.g., <code>for (ProcessState p : sstate.getProcessStates())</code>.
	 * Alternatively, you can invoke the <code>iterator()</code> method to get
	 * an <code>Iterator</code>.
	 * 
	 * @return iterable object yielding all the process states in this state
	 */
	Iterable<? extends ProcessState> getProcessStates();

	/**
	 * Sets the path condition to the given value. This will either modify this
	 * state (if the state is mutable) or return a new state (if not).
	 * 
	 * @param pathCondition
	 *            a boolean-valued symbolic expression
	 * @return state modified to have new path condition
	 */
	State setPathCondition(BooleanExpression pathCondition);

	/**
	 * How many processes can reach this dynamic scope? A process p can reach a
	 * dynamic scope d iff there is a path starting from a dynamic scope which
	 * is referenced in a frame on p's call stack to d, following the "parent"
	 * edges in the scope tree.
	 * 
	 * @return the number of processes which can reach this dynamic scope
	 */
	int numberOfReachers(int sid);

	/**
	 * Is this dynamic scope reachable by the process with the given PID?
	 * 
	 * @param pid
	 *            the process ID (PID)
	 * @return true iff this dynamic scope is reachable from the process with
	 *         pid PID
	 */
	boolean reachableByProcess(int sid, int pid);

	/**
	 * Updates the value of a variable in this state. Returns either a new state
	 * or this one, depending on whether this state is mutable.
	 * 
	 * @param variable
	 *            The dynamic variable to update.
	 * @param scopeID
	 *            The dynamic scope ID of the dynamic scope containing the
	 *            variable.
	 * @param value
	 *            The new value to be assigned to the variable.
	 * @return A state that is the old state modified by updating the value of
	 *         the variable.
	 */
	State setVariable(int vid, int scopeId, SymbolicExpression value);

	int getCanonicId();

}
