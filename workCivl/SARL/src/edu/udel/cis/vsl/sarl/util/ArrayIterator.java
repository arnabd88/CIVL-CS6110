package edu.udel.cis.vsl.sarl.util;

import java.util.Iterator;

public class ArrayIterator<E> implements Iterator<E> {

	private E[] array;

	private int index = 0;

	private int length;

	public ArrayIterator(E[] array) {
		this.array = array;
		this.length = array.length;
	}

	@Override
	public boolean hasNext() {
		return index < length;
	}

	@Override
	public E next() {
		E result = array[index];

		index++;
		return result;
	}

}
