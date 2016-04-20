package edu.udel.cis.vsl.civl.state.persistent;

import java.util.ArrayList;
import java.util.Iterator;

import com.github.krukow.clj_ds.PersistentVector;
import com.github.krukow.clj_ds.Persistents;

/**
 * Partial implementation of an immutable vector. Wraps a Clojure
 * PersistentVector and extends PersistentObject. This combines the Clojure
 * features with the support for caching hash functions and the Flyweight
 * Pattern.
 * 
 * This class is abstract; subclasses still have to implement {#link
 * {@link PersistentObject#canonizeChildren(edu.udel.cis.vsl.sarl.IF.SymbolicUniverse, java.util.Map)}
 * 
 * @author siegel
 * 
 * @param <T>
 *            any type, the type of the elements of this vector
 */
public abstract class CIVLVector<T> extends PersistentObject implements
		Iterable<T> {

	/************************ Instance Fields ************************/

	/**
	 * The elements of this vector; a Clojure persistent vector.
	 */
	protected PersistentVector<T> values;

	/************************** Constructors *************************/

	/**
	 * Constructs new vector wrapping the given Clojure vector.
	 * 
	 * @param values
	 *            the Clojure vector
	 */
	CIVLVector(PersistentVector<T> values) {
		this.values = values;
	}

	/**
	 * Creates new empty vector.
	 */
	CIVLVector() {
		this.values = Persistents.vector();
	}

	/**
	 * Creates vector (X,X,...,X) where X occurs multiplicity times.
	 * 
	 * @param value
	 *            the element X
	 * @param multiplicity
	 *            number of times to use this element, i.e., the length of the
	 *            new vector
	 */
	CIVLVector(T value, int multiplicity) {
		ArrayList<T> vals = new ArrayList<T>(multiplicity);

		for (int i = 0; i < multiplicity; i++)
			vals.add(value);
		values = Persistents.<T> vector(vals);
	}

	/************************ Abstract Methods ***********************/

	protected abstract CIVLVector<T> newVector(PersistentVector<T> values);

	/******************** Package-private Methods ********************/

	PersistentVector<T> getValues() {
		return values;
	}

	CIVLVector<T> set(int index, T value) {
		return value == values.get(index) ? this : newVector(values.plusN(
				index, value));
	}

	CIVLVector<T> remove(int index) {
		PersistentVector<T> newValues = values;
		int n = values.size() - 1;

		for (int i = index; i < n; i++)
			newValues = newValues.plusN(i, values.get(i + 1));
		newValues = newValues.minus();
		return newVector(newValues);
	}

	/********************** Methods from Iterable ********************/

	@Override
	public Iterator<T> iterator() {
		return values.iterator();
	}

	/****************** Methods from PersistentObject ****************/

	@Override
	protected int computeHashCode() {
		return values.hashCode();
	}

	@Override
	protected boolean computeEquals(PersistentObject that) {
		return that instanceof CIVLVector
				&& values.equals(((CIVLVector<?>) that).values);
	}

	/********************** Other public methods *********************/

	public int size() {
		return values.size();
	}

	public T get(int index) {
		return values.get(index);
	}

}
