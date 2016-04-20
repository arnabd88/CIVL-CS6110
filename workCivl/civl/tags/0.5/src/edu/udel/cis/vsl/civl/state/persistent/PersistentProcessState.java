package edu.udel.cis.vsl.civl.state.persistent;

import java.io.PrintStream;
import java.util.Iterator;
import java.util.Map;

import com.github.krukow.clj_ds.PersistentStack;

import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.StackEntry;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;

public class PersistentProcessState extends PersistentObject implements
		ProcessState {

	/************************* Static Fields *************************/

	/**
	 * The hash code of this class, used in the hash code method to help
	 * distinguish hash codes of objects in this class from those in other
	 * classes. This can help because objects from different persistent classes
	 * will be mixed in the same hash data structures.
	 */
	private static final int classCode = PersistentProcessState.class
			.hashCode();

	/************************ Instance Fields ************************/

	/**
	 * The process ID (pid).
	 */
	private int pid;

	/**
	 * The call stack, represented as a persistent stack of stack entries.
	 * Method {@link PersistentStack#minus()} is the "pop": "removes" top entry.
	 * Method {@link PersistentStack#plus(Object)} is the "push": "adds" entry
	 * to top of stack. Method {@link PersistentStack#peek()} is the "peek":
	 * returns top entry on stack.
	 * 
	 */
	private CallStack callStack;

	/**
	 * Number of atomic blocks that are being executing in the process.
	 * Incremented when entering an atomic block, and decremented when leaving
	 * it.
	 */
	private int atomicCount = 0;

	/************************** Constructors *************************/

	/**
	 * Constructs new PersistentProcessState with given fields. The fields are
	 * not cloned.
	 * 
	 * @param pid
	 *            the process ID, a nonnegative int
	 * @param callStack
	 *            the call stack
	 * @param atomicCount
	 *            the atomic count
	 */
	PersistentProcessState(int pid, CallStack callStack, int atomicCount) {
		this.pid = pid;
		this.callStack = callStack;
		this.atomicCount = atomicCount;
	}

	/**
	 * Constructs new process state with given pid, empty call stack, and atomic
	 * count of 0.
	 * 
	 * @param pid
	 *            the process ID, a nonnegative int
	 */
	PersistentProcessState(int pid) {
		this(pid, CallStack.emptyStack, 0);
	}

	/******************** Package-private Methods ********************/

	CallStack getCallStack() {
		return callStack;
	}

	/**
	 * Returns process state equivalent to this one except that PID has given
	 * value.
	 * 
	 * @param pid
	 *            a nonnegative int, the process ID
	 * @return process state equivalent to this but with new pid
	 */
	PersistentProcessState setPid(int pid) {
		return pid == this.pid ? this : new PersistentProcessState(pid,
				callStack, atomicCount);
	}

	/**
	 * Returns process state equivalent to this one except that call stack has
	 * given value.
	 * 
	 * @param callStack
	 *            the new call stack
	 * @return process state equivalent to this but with new call stack
	 */
	PersistentProcessState setCallStack(CallStack callStack) {
		return callStack == this.callStack ? this : new PersistentProcessState(
				pid, callStack, atomicCount);
	}

	/**
	 * Returns process state equivalent to this one except that atomic count has
	 * given value.
	 * 
	 * @param atomicCount
	 *            a nonnegative int, the new value for atomic count
	 * @return process state equivalent to this but with new atomic count
	 */
	PersistentProcessState setAtomicCount(int atomicCount) {
		return atomicCount == this.atomicCount ? this
				: new PersistentProcessState(pid, callStack, atomicCount);
	}

	/**
	 * Returns process state obtained by popping the call stack (i.e., removing
	 * the top entry). Note that this is not modified, since it is immutable.
	 * 
	 * Behavior is undefined if call stack is empty.
	 * 
	 * @return process state equivalent to this one but with top entry removed
	 *         from call stack
	 */
	PersistentProcessState pop() {
		return new PersistentProcessState(pid, callStack.pop(), atomicCount);
	}

	/**
	 * Returns process state obtained by pushing the given frame onto the call
	 * stack. Note that this is not modified, since it is immutable.
	 * 
	 * @return process state equivalent to this one but with new entry pushed
	 *         onto top of stack
	 */
	PersistentProcessState push(PersistentStackEntry newStackEntry) {
		return new PersistentProcessState(pid, callStack.push(newStackEntry),
				atomicCount);
	}

	/**
	 * Returns process state obtained by replacing top entry on stack with
	 * specified entry. Note that this is not modified, since it is immutable.
	 * Equivalent to doing a pop, then push.
	 * 
	 * @return process state equivalent to this one but with top stack entry
	 *         replaced by given one
	 */
	PersistentProcessState replaceTop(PersistentStackEntry newStackEntry) {
		return new PersistentProcessState(pid,
				callStack.replaceTop(newStackEntry), atomicCount);
	}

	PersistentProcessState renumberScopes(int[] oldToNew) {
		return setCallStack(callStack.renumberScopes(oldToNew));
	}

	/****************** Methods from PersistentObject ****************/

	@Override
	protected PersistentProcessState canonize(SymbolicUniverse universe,
			Map<PersistentObject, PersistentObject> canonicMap) {
		return (PersistentProcessState) super.canonize(universe, canonicMap);
	}

	@Override
	protected int computeHashCode() {
		return classCode ^ callStack.hashCode() ^ (514229 * pid)
				^ (39916801 * atomicCount);
	}

	@Override
	protected boolean computeEquals(PersistentObject obj) {
		if (obj instanceof PersistentProcessState) {
			PersistentProcessState that = (PersistentProcessState) obj;

			return pid == that.pid && atomicCount == that.atomicCount
					&& callStack.equals(that.callStack);
		}
		return false;
	}

	@Override
	protected void canonizeChildren(SymbolicUniverse universe,
			Map<PersistentObject, PersistentObject> canonicMap) {
		callStack = callStack.canonize(universe, canonicMap);
	}

	/*********************** Methods from Object *********************/

	@Override
	public String toString() {
		return "State of process " + pid + " (call stack length = "
				+ callStack.size() + ")";
	}

	/******************* Methods from ProcessState *******************/

	@Override
	public boolean hasEmptyStack() {
		return callStack.isEmpty();
	}

	@Override
	public Location getLocation() {
		return callStack.peek().location();
	}

	@Override
	public int getPid() {
		return pid;
	}

	@Override
	public int getDyscopeId() {
		return callStack.peek().scope();
	}

	@Override
	public StackEntry peekStack() {
		return callStack.peek();
	}

	@Override
	public int stackSize() {
		return callStack.size();
	}

	@Override
	public Iterable<PersistentStackEntry> getStackEntries() {
		return callStack;
	}

	@Override
	public Iterator<PersistentStackEntry> bottomToTopIterator() {
		return callStack.iterator();
	}

	@Override
	public boolean isPurelyLocalProc() {
		// TODO: this result should be stored in the location.
		for (Statement s : getLocation().outgoing())
			if (!s.isPurelyLocal())
				return false;
		return true;
	}

	@Override
	public void print(PrintStream out, String prefix) {

		out.println(prefix + "process " + pid);
		out.println(prefix + "| atomicCount = " + atomicCount);
		callStack.print(out, prefix + "| ");
		out.flush();
	}

	@Override
	public PersistentProcessState incrementAtomicCount() {
		return new PersistentProcessState(pid, callStack, atomicCount + 1);
	}

	@Override
	public PersistentProcessState decrementAtomicCount() {
		return new PersistentProcessState(pid, callStack, atomicCount - 1);
	}

	@Override
	public boolean inAtomic() {
		return atomicCount > 0;
	}

	@Override
	public int atomicCount() {
		return atomicCount;
	}

}
