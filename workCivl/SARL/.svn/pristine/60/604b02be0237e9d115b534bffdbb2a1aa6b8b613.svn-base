/*******************************************************************************
 * Copyright (c) 2013 Stephen F. Siegel, University of Delaware.
 * 
 * This file is part of SARL.
 * 
 * SARL is free software: you can redistribute it and/or modify it under the
 * terms of the GNU Lesser General Public License as published by the Free
 * Software Foundation, either version 3 of the License, or (at your option) any
 * later version.
 * 
 * SARL is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
 * A PARTICULAR PURPOSE. See the GNU Lesser General Public License for more
 * details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with SARL. If not, see <http://www.gnu.org/licenses/>.
 ******************************************************************************/
package edu.udel.cis.vsl.sarl.IF.object;

import edu.udel.cis.vsl.sarl.IF.Transform;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * A finite ordered immutable sequence of symbolic expressions.
 * 
 * @author siegel
 *
 * @param <T>
 *            the element type
 */
public interface SymbolicSequence<T extends SymbolicExpression>
		extends SymbolicObject, Iterable<T> {

	/**
	 * Returns the number of elements in this sequence.
	 * 
	 * @return the number of elements in this sequence
	 */
	int size();

	/**
	 * Returns the "first" element of this collection or null if the collection
	 * is empty. For ordered collections, first means what you expect; for
	 * unordered collections it is some fixed element.
	 * 
	 * @return the first element.
	 */
	T getFirst();

	/**
	 * Gets the <code>index</code>-th element of this sequence
	 * 
	 * @return the <code>index</code>-th element of this sequence
	 * @throws RuntimeException
	 *             if index is negative or greater than or equal to the size
	 */
	T get(int index);

	/**
	 * Appends an element to the end of a sequence.
	 * 
	 * @param element
	 *            a symbolic expression
	 * @return a sequence identical to the given one except with the given
	 *         element added to the end
	 */
	SymbolicSequence<T> add(T element);

	/**
	 * "Sets" the element at specified position, or, more precisely, returns a
	 * new sequence identical to this except with the element at the specified
	 * index set to the given element. Sequence must have length at least
	 * index+1.
	 * 
	 * @param index
	 *            integer in range [0,n-1], where n is length of sequence
	 * @param element
	 *            a symbolic expression
	 * @return a sequence identical to this except that element in position
	 *         <code>index</code> now has value <code>element</code>
	 */
	SymbolicSequence<T> set(int index, T element);

	/**
	 * "Removes" the element at position index, shifting all subsequent elements
	 * down one; more precisely, returns a new sequence obtained by removing
	 * that element from this sequence.
	 * 
	 * @param index
	 *            integer in range [0,n-1], where n is length of sequence
	 * @return a sequence obtained from given one by removing the element and
	 *         shifting remaining element down one in index
	 */
	SymbolicSequence<T> remove(int index);

	/**
	 * Inserts element at position index, shifting all subsequence elements up
	 * one.
	 * 
	 * @param index
	 *            integer in range [0,n], where n is length of sequence. If
	 *            index is n, this is equivalent to appending the element to the
	 *            end of the sequence
	 * @param element
	 *            the element to insert into the sequence
	 * @return a sequence obtained from given one by inserting the element at
	 *         the specified index
	 */
	SymbolicSequence<T> insert(int index, T element);

	/**
	 * If index is less than the original size s, same as set. Otherwise returns
	 * a sequence of length index+1, with the elements in positions s, s+1, ...,
	 * index-1 set to filler, and the element in position index set to value,
	 * and all other elements as in the original.
	 * 
	 * @param index
	 *            position to set
	 * @param value
	 *            new value for element at position
	 * @param filler
	 *            element to be inserted in newly created empty slots
	 * @return a new sequence, possibly extended with filler, in which element
	 *         at position index is value
	 */
	SymbolicSequence<T> setExtend(int index, T value, T filler);

	/**
	 * Returns the subsequence whose first element is the element at position
	 * start and last element is the element at position end-1. The length of
	 * the subsequence is therefore end-start.
	 * 
	 * @param start
	 *            index of first element
	 * @param end
	 *            one more than then index of last element
	 * @return the subsequence
	 */
	SymbolicSequence<T> subSequence(int start, int end);

	/**
	 * Returns a sequence obtained by applying a function to every element of
	 * this sequence; also known as "map".
	 * 
	 * @param <U>
	 *            target type of transformation
	 * @param transform
	 *            a function from <code>T</code> to <code>U</code>
	 * @return a sequence of same length as this one obtained by applying
	 *         <code>transform</code> to each element
	 */
	<U extends SymbolicExpression> SymbolicSequence<U> apply(
			Transform<T, U> transform);

	/**
	 * Returns the number of "NULL" elements of this sequence, i.e., symbolic
	 * expressions for which method {@link SymbolicExpression#isNull()} returns
	 * <code>true</code>.
	 * 
	 * @return number of NULL symbolic expressions in this sequence
	 */
	int getNumNull();
}
