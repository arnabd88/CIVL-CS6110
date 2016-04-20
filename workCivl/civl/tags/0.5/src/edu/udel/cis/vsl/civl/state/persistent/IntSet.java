package edu.udel.cis.vsl.civl.state.persistent;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.Map;

import com.github.krukow.clj_ds.PersistentSet;
import com.github.krukow.clj_ds.Persistents;

import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;

/**
 * An immutable set of integers.
 * 
 * @author siegel
 * 
 */
public class IntSet extends PersistentObject implements Iterable<Integer> {

	/************************* Static Fields *************************/

	/**
	 * The hash code of this class, used in the hash code method to help
	 * distinguish hash codes of objects in this class from those in other
	 * classes. This can help because objects from different persistent classes
	 * will be mixed in the same hash data structures.
	 */
	private final static int classCode = IntSet.class.hashCode();

	private final static PersistentSet<Integer> emptySortedSet = Persistents
			.treeSet();

	private static ArrayList<IntSet> singletons = new ArrayList<IntSet>();

	/************************ Instance Fields ************************/

	private PersistentSet<Integer> set;

	/************************** Constructors *************************/

	IntSet(PersistentSet<Integer> set) {
		this.set = set;
	}

	/**
	 * Constructs singleton set containing a.
	 * 
	 * @param a
	 *            an int
	 */
	IntSet(int a) {
		this.set = emptySortedSet.plus(a);
	}

	/************************ Static Methods *************************/

	public static IntSet singleton(int n) {
		IntSet result;

		while (n >= singletons.size())
			singletons.add(null);
		result = singletons.get(n);
		if (result == null) {
			result = new IntSet(n);
			singletons.set(n, result);
		}
		return result;
	}

	/******************** Package-private Methods ********************/

	/*********************** Methods from Object *********************/

	@Override
	public String toString() {
		StringBuffer buf = new StringBuffer();
		boolean first = true;

		buf.append('{');
		for (Integer j : this) {
			if (first)
				first = false;
			else
				buf.append(',');
			buf.append(j);
		}
		buf.append('}');
		return buf.toString();
	}

	/********************** Methods from Iterable ********************/

	@Override
	public Iterator<Integer> iterator() {
		return set.iterator();
	}

	/****************** Methods from PersistentObject ****************/

	@Override
	protected int computeHashCode() {
		return classCode ^ set.hashCode();
	}

	@Override
	protected boolean computeEquals(PersistentObject that) {
		return that instanceof IntSet && set.equals(((IntSet) that).set);
	}

	@Override
	protected void canonizeChildren(SymbolicUniverse universe,
			Map<PersistentObject, PersistentObject> canonicMap) {
		// nothing to do
	}

	@Override
	protected IntSet canonize(SymbolicUniverse universe,
			Map<PersistentObject, PersistentObject> canonicMap) {
		return (IntSet) super.canonize(universe, canonicMap);
	}

	/********************** Other public methods *********************/

	public int size() {
		return set.size();
	}

	public boolean contains(int value) {
		return set.contains(value);
	}

	public IntSet add(int a) {
		if (set.contains(a))
			return this;
		return new IntSet(set.plus(a));
	}

	public IntSet remove(int a) {
		if (!set.contains(a))
			return this;
		return new IntSet(set.minus(a));
	}

	/**
	 * Given set of integers S, returns set S' obtained from S by shifting
	 * elements greather than start down by 1, i.e.:
	 * 
	 * <pre>
	 * b in S' iff (b<start && b in S) || (b>=start && b+1 in S)
	 * </pre>
	 * 
	 * Example: start=3, S={2,3,5,10}. S'={2,4,9}.
	 * 
	 * @param start
	 *            an integer
	 * @return S'
	 */
	public IntSet shiftDown(int start) {
		PersistentSet<Integer> newSet = emptySortedSet;

		for (int a : set) {
			if (a < start)
				newSet = newSet.plus(a);
			else if (a > start)
				newSet = newSet.plus(a - 1);
		}
		return newSet == set ? this : new IntSet(newSet);
	}
}
