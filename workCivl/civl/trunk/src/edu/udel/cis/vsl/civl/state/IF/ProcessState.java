package edu.udel.cis.vsl.civl.state.IF;

import java.io.PrintStream;
import java.util.Iterator;
import java.util.Map;

import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * A ProcessState represents the state of a process (thread of execution) in a
 * CIVL model. The process has an integer ID number, the PID, unique among the
 * processes in the state.
 * 
 * The state of the process is essentially a call stack. The entries on the
 * stack are "activation frames", instances of {@link StackEntry}.
 * 
 * @author siegel
 * 
 */
public interface ProcessState {

	/**
	 * Does this process state have an empty call stack?
	 * 
	 * @return true iff the call stack is empty
	 */
	boolean hasEmptyStack();

	/**
	 * Returns the location at the top of the call stack of this process.
	 * Undefined behavior if stack is empty.
	 * 
	 * @return location at top of call stack
	 */
	Location getLocation();

	/**
	 * Returns the process ID (pid) of this process state. Within a fixed state,
	 * every process is assigned an integer ID which is unique. It does not
	 * necessarily stay the same from state to state though.
	 * 
	 * @return the PID of the process
	 */
	int getPid();

	/**
	 * The ID of the dynamic scope of the top frame on the call stack. Undefined
	 * behavior if call stack is empty.
	 * 
	 * @return the dyscope id of the dyscope on the top frame of the call stack
	 */
	int getDyscopeId();

	/**
	 * Returns the top frame on the call stack. Undefined behavior if call stack
	 * is empty.
	 * 
	 * @return top frame on call stack.
	 */
	StackEntry peekStack();

	/**
	 * Returns the second top frame on the call stack. Return NULL if the
	 * process has fewer than two stacks.
	 * 
	 * @return top frame on call stack.
	 */
	StackEntry peekSecondLastStack();

	/**
	 * Returns the length of the call stack.
	 * 
	 * @return the length of the call stack
	 */
	int stackSize();

	/**
	 * Returns an iterable object over the entries in this stack. Order is fixed
	 * (will be the same each time this method is called), but not specified.
	 * 
	 * @return the entries in the stack
	 */
	Iterable<? extends StackEntry> getStackEntries();

	/**
	 * Returns an iterator over the entries in the call stack from the bottom to
	 * the top.
	 * 
	 * @return iterator from bottom to top
	 */
	Iterator<? extends StackEntry> bottomToTopIterator();

	/**
	 * Prints a human-readable form of this process state.
	 * 
	 * @param out
	 *            print stream to which the output is sent
	 * @param prefix
	 *            a string to prepend to each line of output
	 */
	void print(PrintStream out, String prefix);

	/**
	 * Increase the atomic block counter. Invoked when encountering a new atomic
	 * block.
	 * 
	 * @return A new process state with the atomic block counter increased by
	 *         one and other fields remain unchanged.
	 */
	ProcessState incrementAtomicCount();

	/**
	 * Decrease the atomic block counter. Invoked when reaching the end of a
	 * certain atomic block.
	 * 
	 * @return A new process state with the atomic block counter decreased by
	 *         one and other fields remain unchanged.
	 */
	ProcessState decrementAtomicCount();

	/**
	 * Check if the current process is in the execution of some atomic block.
	 * 
	 * @return True if the current process is executing some atomic block.
	 */
	boolean inAtomic();

	/**
	 * 
	 * @return The number of $atomic blocks that are currently being executed in
	 *         this process
	 */
	int atomicCount();

	/**
	 * This identifier is not part of the state. It is never renamed, helping to
	 * identify a specific process when processes get collected.
	 * 
	 * @return The identifier of this process.
	 */
	int identifier();

	StringBuffer toStringBuffer(String prefix);

	/**
	 * This name is not part of the state. It is immutable and never renamed,
	 * helping to identify a specific process when processes get collected.
	 * 
	 * @return The name of this process, in the form of ,<code>p</code>
	 *         +identifier, e.g. <code>p2</code>, <code>p3</code>.
	 */
	String name();

	Map<SymbolicExpression, Boolean> getReachableMemUnitsWoPointer();

	Map<SymbolicExpression, Boolean> getReachableMemUnitsWtPointer();

	StringBuffer toSBrieftringBuffer();
}
