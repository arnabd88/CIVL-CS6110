package edu.udel.cis.vsl.civl.state.persistent;

import java.io.PrintStream;
import java.util.Iterator;
import java.util.Map;

import com.github.krukow.clj_ds.PersistentStack;
import com.github.krukow.clj_ds.PersistentVector;
import com.github.krukow.clj_ds.Persistents;

import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;

/**
 * Represents the call stack of a process in a CIVL program. Part of the state
 * of that process. The call stack is represented as a persistent vector of
 * stack entries.
 * 
 * @author siegel
 */
public class CallStack extends PersistentObject implements
		Iterable<PersistentStackEntry> {

	/************************* Static Fields *************************/

	/**
	 * The hash code of this class, used in the hash code method to help
	 * distinguish hash codes of objects in this class from those in other
	 * classes. This can help because objects from different persistent classes
	 * will be mixed in the same hash data structures.
	 */
	private final static int classCode = CallStack.class.hashCode();

	/**
	 * The empty call stack. This is a constant. Since this class is immutable,
	 * there is only a need for one instance of the empty stack. If you need an
	 * empty, use this one instead of instantiating a new one, for best
	 * performance.
	 */
	final static CallStack emptyStack = new CallStack();

	/************************ Instance Fields ************************/

	/**
	 * The immutable data structure containing the actual entries on this call
	 * stack. Uses Clojure's PersistentVector.
	 * 
	 * Method {@link PersistentStack#minus()} is the "pop": "removes" top entry.
	 * Method {@link PersistentStack#plus(Object)} is the "push": "adds" entry
	 * to top of stack. Method {@link PersistentStack#peek()} is the "peek":
	 * returns top entry on stack.
	 */
	private PersistentVector<PersistentStackEntry> entries;

	/************************** Constructors *************************/

	/**
	 * Constructs new CallStack wrapping the given vector of stack entries. The
	 * data is not cloned.
	 * 
	 * @param entries
	 *            persistent vector of stack entries with position 0 being the
	 *            bottom of the stack.
	 */
	CallStack(PersistentVector<PersistentStackEntry> entries) {
		this.entries = entries;
	}

	/**
	 * Constructs an empty call stack.
	 */
	private CallStack() {
		this.entries = Persistents.<PersistentStackEntry> vector();
	}

	/******************** Package-private Methods ********************/

	PersistentStack<PersistentStackEntry> getEntries() {
		return entries;
	}

	CallStack renumberScopes(int[] oldToNew) {
		int size = size();
		PersistentVector<PersistentStackEntry> newEntries = entries;

		for (int i = 0; i < size; i++) {
			PersistentStackEntry oldEntry = entries.get(i);
			PersistentStackEntry newEntry = oldEntry.setScope(oldToNew[oldEntry
					.scope()]);

			if (oldEntry != newEntry)
				newEntries = newEntries.plusN(i, newEntry);
		}
		return newEntries == entries ? this : new CallStack(newEntries);
	}

	/********************** Methods from Iterable ********************/

	@Override
	public Iterator<PersistentStackEntry> iterator() {
		return entries.iterator();
	}

	/****************** Methods from PersistentObject ****************/

	@Override
	protected int computeHashCode() {
		return classCode ^ entries.hashCode();
	}

	@Override
	protected boolean computeEquals(PersistentObject obj) {
		return obj instanceof CallStack
				&& entries.equals(((CallStack) obj).entries);
	}

	@Override
	protected void canonizeChildren(SymbolicUniverse universe,
			Map<PersistentObject, PersistentObject> canonicMap) {
		// nothing to do
	}

	@Override
	protected CallStack canonize(SymbolicUniverse universe,
			Map<PersistentObject, PersistentObject> canonicMap) {
		return (CallStack) super.canonize(universe, canonicMap);
	}

	/********************** Other public methods *********************/

	/**
	 * Returns call stack obtained by popping (removing top entry from) this
	 * one. The top entry is the last (highest index) entry.
	 * 
	 * Precondition: the stack is not empty. Otherwise behavior is undefined
	 * 
	 * @return call stack obtained by popping this one
	 */
	public CallStack pop() {
		return new CallStack(entries.minus());
	}

	/**
	 * Returns the top entry on this call stack.
	 * 
	 * Precondition: the stack is not empty. Otherwise behavior is undefined
	 * 
	 * @return top entry
	 */
	public PersistentStackEntry peek() {
		return entries.peek();
	}

	/**
	 * Returns call stack obtained by pushing the given entry onto the stack.
	 * 
	 * @param entry
	 *            a stack entry
	 * @return call stack obtained by pushing entry onto this stack
	 */
	public CallStack push(PersistentStackEntry entry) {
		return new CallStack(entries.plus(entry));
	}

	/**
	 * Returns call stack obtained by replacing the top entry on this stack with
	 * the given one. Equivalent to popping then pushing.
	 * 
	 * Precondition: the stack is not empty. Otherwise behavior is undefined
	 * 
	 * @param entry
	 *            a call stack entry
	 * @return call stack obtained by replacing top entry with given one
	 * 
	 */
	public CallStack replaceTop(PersistentStackEntry entry) {
		if (entry == entries.peek())
			return this;
		return new CallStack(entries.minus().plus(entry));
	}

	/**
	 * Returns the number of entries in this call stack.
	 * 
	 * @return number of entries
	 */
	public int size() {
		return entries.size();
	}

	/**
	 * Is this stack empty?
	 * 
	 * @return true iff stack is empty (i.e., has 0 entries)
	 */
	public boolean isEmpty() {
		return entries.isEmpty();
	}

	/**
	 * Prints a human-readable representation of this stack.
	 * 
	 * @param out
	 *            output stream to which to send output
	 * @param prefix
	 *            a string to prepend to each line of output
	 */
	public void print(PrintStream out, String prefix) {
		int numFrames = entries.size();

		out.println(prefix + "call stack");
		for (int i = numFrames - 1; i >= 0; i--)
			out.println(prefix + "| " + entries.get(i));
		out.flush();
	}

}
