package edu.udel.cis.vsl.civl.util.IF;

import java.util.Iterator;
import java.util.NoSuchElementException;

public class Singleton<T> implements Iterable<T> {

	private T element;

	public Singleton(T element) {
		this.element = element;
	}

	@Override
	public String toString() {
		return "{" + element + "}";
	}

	@Override
	public Iterator<T> iterator() {
		return new Iterator<T>() {

			private boolean done = false;

			@Override
			public boolean hasNext() {
				return !done;
			}

			@Override
			public T next() {
				if (done)
					throw new NoSuchElementException();
				done = true;
				return element;
			}

			@Override
			public void remove() {
				throw new UnsupportedOperationException();
			}
		};
	}

}
