package edu.udel.cis.vsl.sarl.util;

import java.util.Iterator;

/**
 * Simple implementation of {@link Iterable} backed by an array. Assumes the
 * array will not be modified, else all bets are off.
 * 
 * @author siegel
 *
 * @param <T>
 *            element type
 */
public class ArrayIterable<T> implements Iterable<T> {

	private T[] a;

	private int length;

	public ArrayIterable(T[] a) {
		this.a = a;
		this.length = a.length;
	}

	private class ArrayIterator implements Iterator<T> {
		private int nextIndex = 0;

		@Override
		public boolean hasNext() {
			return nextIndex < length;
		}

		@Override
		public T next() {
			T result = a[nextIndex];

			nextIndex++;
			return result;
		}
	}

	@Override
	public Iterator<T> iterator() {
		return new ArrayIterator();
	}
}
