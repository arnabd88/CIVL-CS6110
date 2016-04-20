/**
 * 
 */
package edu.udel.cis.vsl.civl.state.trans;

import java.io.PrintStream;
import java.util.ArrayDeque;
import java.util.Iterator;

import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.StackEntry;

/**
 * A standard implementation of {@link ProcessState}.
 * 
 * @author Stephen F. Siegel (siegel)
 * @author Timothy K. Zirkel (zirkel)
 * @author Timothy J. McClory (tmcclory)
 * 
 */
public class TransientProcessState extends TransientObject implements
		ProcessState {

	/*********************** Static Fields **************************/

	/**
	 * Print debugging info?
	 */
	@SuppressWarnings("unused")
	private static boolean debug = false;

	/**
	 * How many instances of this class have been created?
	 */
	static long instanceCount = 0;

	/********************** Instance Fields *************************/

	/**
	 * The process ID (pid), part of the "intrinsic data" of this class.
	 */
	private int pid;

	/**
	 * The call stack, part of the "intrinsic data" of this class. A non-null
	 * ArrayDeque uses as a stack. Entry 0 is the TOP of the stack.
	 */
	private ArrayDeque<StackEntry> callStack;

	/************************ Construtors ***************************/

	/**
	 * Constructs a new process state with empty stack and given PID.
	 * 
	 * @param pid
	 *            The unique process ID.
	 */
	TransientProcessState(int pid) {
		super(instanceCount++);
		this.pid = pid;
		callStack = new ArrayDeque<>();
	}

	/**
	 * Constructs a new process state with given PID and stack. Note the stack
	 * is NOT copied.
	 * 
	 * @param pid
	 *            the process ID (PID)
	 * @param stack
	 *            the call stack
	 */
	TransientProcessState(int pid, ArrayDeque<StackEntry> stack) {
		super(instanceCount++);
		assert stack != null;
		this.pid = pid;
		callStack = stack;
	}

	/****************** Package Private Methods **********************/

	TransientProcessState push(StackEntry newStackEntry) {
		if (mutable) {
			callStack.push(newStackEntry);
			return this;
		} else {
			ArrayDeque<StackEntry> newStack = callStack.clone();

			newStack.push(newStackEntry);
			return new TransientProcessState(pid, newStack);
		}
	}

	TransientProcessState pop() {
		if (mutable) {
			callStack.pop();
			return this;
		} else {
			ArrayDeque<StackEntry> newStack = callStack.clone();

			newStack.pop();
			return new TransientProcessState(pid, newStack);
		}
	}

	TransientProcessState replaceTop(TransientStackEntry newStackEntry) {
		return pop().push(newStackEntry);
	}

	TransientProcessState setPid(int pid) {
		if (mutable) {
			this.pid = pid;
			return this;
		}
		return new TransientProcessState(pid, callStack);
	}

	TransientProcessState setStackEntries(ArrayDeque<StackEntry> frames) {
		if (mutable) {
			this.callStack = frames;
			return this;
		}
		return new TransientProcessState(pid, frames);
	}

	// TODO: make stack entries transient, then this will
	// be more efficient:
	TransientProcessState updateScopes(int[] oldToNewSidMap) {
		int stackSize = callStack.size();
		ArrayDeque<StackEntry> stack = new ArrayDeque<>(stackSize);
		Iterator<StackEntry> iter = callStack.descendingIterator(); // bottom
																	// first
		boolean changeStack = false;

		while (iter.hasNext()) {
			StackEntry frame = iter.next();
			int oldScope = frame.scope();
			int newScope = oldToNewSidMap[oldScope];

			assert newScope >= 0;
			if (oldScope != newScope) {
				frame = new TransientStackEntry(frame.location(), newScope);
				changeStack = true;
			}
			stack.push(frame);
		}
		if (changeStack)
			return setStackEntries(stack);
		return this;
	}

	/**
	 * Changes the location of the top frame on this process' call stack. As
	 * usual, if this process state is mutable, it modifies this process state
	 * and return this; otherwise it returns a new process state and leaves this
	 * one unmodified.
	 * 
	 * Preconditions: (1) the call stack must be non-empty; (2) the top frame of
	 * the call stack must have a dynamic scope for which the corresponding
	 * static scope contains the given location.
	 * 
	 * @param location
	 *            a location in the static scope corresponding to the dynamic
	 *            scope of the top frame of the call stack
	 * @return process state with top frame of call stack modified to reflect
	 *         the new location
	 */
	TransientProcessState setLocation(Location location) {
		StackEntry peek = callStack.peek();

		if (peek.location() == location)
			return this;
		if (mutable) {
			callStack.pop();
			callStack.push(new TransientStackEntry(location, peek.scope()));
			return this;
		} else {
			ArrayDeque<StackEntry> newStack = callStack.clone();

			newStack.pop();
			newStack.push(new TransientStackEntry(location, peek.scope()));
			return new TransientProcessState(pid, newStack);
		}
	}

	/********************* Methods from Object ***********************/

	@Override
	public String toString() {
		return "ProcessState " + identifier() + " [pid=" + pid + "]";
	}

	/***************** Methods from TransientObject ******************/

	@Override
	protected int computeHashCode() {
		int result = 31 * pid;

		for (StackEntry frame : callStack)
			result ^= frame.hashCode();
		return result;
	}

	@Override
	protected boolean computeEquals(Object object) {
		if (object instanceof TransientProcessState) {
			TransientProcessState that = (TransientProcessState) object;

			if (pid != that.pid)
				return false;
			if (callStack.size() != that.callStack.size())
				return false;
			else {
				Iterator<StackEntry> iter1 = this.callStack.iterator();
				Iterator<StackEntry> iter2 = that.callStack.iterator();

				while (iter1.hasNext())
					if (!iter1.next().equals(iter2.next()))
						return false;
				return true;
			}
		}
		return false;
	}

	/****************** Methods from ProcessState ********************/

	/**
	 * @return The unique process ID.
	 */
	@Override
	public int getPid() {
		return pid;
	}

	@Override
	public boolean hasEmptyStack() {
		return callStack.size() == 0;
	}

	/**
	 * @return The current location of this process.
	 */
	@Override
	public Location getLocation() {
		return callStack.peek().location();
	}

	/**
	 * @return The id of the current dynamic scope of this process.
	 */
	@Override
	public int getDyscopeId() {
		return callStack.peek().scope();
	}

	/**
	 * Look at the first entry on the call stack, but do not remove it.
	 * 
	 * @return The first entry on the call stack. Null if empty.
	 */

	@Override
	public StackEntry peekStack() {
		return callStack.peek();
	}

	@Override
	public int stackSize() {
		return callStack.size();
	}

	@Override
	public void print(PrintStream out, String prefix) {
		Iterator<StackEntry> iter = callStack.iterator();

		out.println(prefix + "Process State " + identifier() + " [pid=" + pid
				+ "] call stack");
		while (iter.hasNext()) {
			StackEntry frame = iter.next();

			out.println(prefix + "| " + frame);
		}
		out.flush();
	}

	@Override
	public boolean isPurelyLocalProc() {
		for (Statement s : getLocation().outgoing()) {
			if (!s.isPurelyLocal())
				return false;
		}
		return true;
	}

	@Override
	public Iterable<StackEntry> getStackEntries() {
		return callStack;
	}

	@Override
	public Iterator<StackEntry> bottomToTopIterator() {
		return callStack.descendingIterator();
	}

	@Override
	public ProcessState incrementAtomicCount() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public ProcessState decrementAtomicCount() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean inAtomic() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public int atomicCount() {
		// TODO Auto-generated method stub
		return 0;
	}
}
