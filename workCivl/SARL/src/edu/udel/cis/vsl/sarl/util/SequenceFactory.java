package edu.udel.cis.vsl.sarl.util;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;

public abstract class SequenceFactory<E> {

	public SequenceFactory() {
	}

	protected abstract E[] newArray(int size);

	/**
	 * Constructs sequence from iterating over given elements.
	 * 
	 * @param elements
	 *            some collection of elements of T
	 */
	public E[] sequence(Collection<? extends E> elements) {
		int size = elements.size();
		E[] array = newArray(size);

		elements.toArray(array);
		return array;
	}

	/**
	 * Constructs sequence from iterating over given elements.
	 * 
	 * @param elements
	 *            some iterable of elements of E
	 */
	public E[] sequence(Iterable<? extends E> elements) {
		ArrayList<E> tempList = new ArrayList<E>();

		for (E element : elements)
			tempList.add(element);

		int size = tempList.size();
		E[] array = newArray(size);

		tempList.toArray(array);
		return array;
	}

	/**
	 * Constructs singleton sequence consisting of given element.
	 * 
	 * @param element
	 *            an element of T
	 */
	public E[] singletonSequence(E element) {
		E[] newArray = newArray(1);

		newArray[0] = element;
		return newArray;
	}

	public StringBuffer toStringBuffer(E[] seq) {
		StringBuffer result = new StringBuffer();
		boolean first = true;

		result.append("<");
		for (E element : seq) {
			if (first)
				first = false;
			else
				result.append(",");
			result.append(element.toString());
		}
		result.append(">");
		return result;
	}

	public Iterator<E> iterator(E[] seq) {
		return new ArrayIterator<E>(seq);
	}

	public E[] add(E[] sequence, E element) {
		int size = sequence.length;
		E[] newArray = newArray(size + 1);

		System.arraycopy(sequence, 0, newArray, 0, size);
		newArray[size] = element;
		return newArray;
	}

	public E[] set(E[] sequence, int index, E element) {
		int size = sequence.length;
		E[] newArray = newArray(size);

		System.arraycopy(sequence, 0, newArray, 0, size);
		newArray[index] = element;
		return newArray;
	}

	public E[] remove(E[] sequence, int index) {
		int size = sequence.length;
		E[] newArray = newArray(size - 1);

		System.arraycopy(sequence, 0, newArray, 0, index);
		System.arraycopy(sequence, index + 1, newArray, index,
				size - index - 1);
		return newArray;
	}

	public E[] setExtend(E[] sequence, int index, E value, E filler) {
		int size = sequence.length;

		if (index < size)
			return set(sequence, index, value);
		else {
			E[] newArray = newArray(index + 1);

			System.arraycopy(sequence, 0, newArray, 0, size);
			for (int i = size; i < index; i++)
				newArray[i] = filler;
			newArray[index] = value;
			return newArray;
		}
	}

	public E[] subSequence(E[] sequence, int start, int end) {
		int size = sequence.length;

		if (start == 0 && end == size)
			return sequence;

		E[] newArray = newArray(end - start);

		System.arraycopy(sequence, start, newArray, 0, end - start);
		return newArray;
	}

	// see if this is really needed....

	// public <U extends SymbolicExpression> U[] apply(E[] sequence,
	// Transform<E, U> transform, SequenceFactory<U> thatFactory) {
	// int size = sequence.length;
	//
	// for (int i = 0; i < size; i++) {
	// E t = sequence[i];
	// U u = transform.apply(t);
	//
	// if (t != u) {
	// U[] newArray = thatFactory.newArray(size);
	//
	// System.arraycopy(sequence, 0, newArray, 0, i);
	// newArray[i] = u;
	// for (i++; i < size; i++)
	// newArray[i] = transform.apply(sequence[i]);
	// return newArray;
	// }
	// }
	//
	// // not going to work unless U=E
	// @SuppressWarnings("unchecked")
	// U[] result = (U[]) sequence;
	//
	// return result;
	// }

	public E[] insert(E[] sequence, int index, E element) {
		int size = sequence.length;
		E[] newArray = newArray(size + 1);

		System.arraycopy(sequence, 0, newArray, 0, index);
		newArray[index] = element;
		System.arraycopy(sequence, index, newArray, index + 1, size - index);
		return newArray;
	}

}
