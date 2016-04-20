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
package edu.udel.cis.vsl.sarl.object.common;

import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.object.IF.ObjectFactory;

/**
 * A partial implementation of {@link SymbolicObject}.
 * 
 * @author siegel
 * 
 */
public abstract class CommonSymbolicObject implements SymbolicObject {

	// static fields ...

	private final static int NOT_HASHED = -2;

	private final static int HASHED = -1;

	/**
	 * If true, more detailed string representations of symbolic objects will be
	 * returned by the {@link #toString()} method.
	 */
	private final static boolean debug = false;

	// instance fields ...

	/**
	 * Cached hashCode, set upon first run of {@link #hashCode()}.
	 */
	private int hashCode;

	/**
	 * If this object has not been hashed, <code>id</code> will be
	 * <code>NOT_HASHED</code>. If this object has been hashed, but is not
	 * canonic, <code>id</code> will be <code>HASHED</code>. If this object is
	 * canonic (which implies it has been hashed), <code>id</code> will be
	 * nonnegative and will be the unique ID number among canonic objects. This
	 * means this object is the unique representative of its equivalence class.
	 * -1.
	 */
	private int id = NOT_HASHED;

	// Constructors...

	/**
	 * Instantiates object, initialized <code>id</code> to
	 * <code>NOT_HASHED</code>.
	 * 
	 */
	protected CommonSymbolicObject() {
	}

	// Methods...

	public boolean isCanonic() {
		return id >= 0;
	}

	/**
	 * Sets the id.
	 * 
	 * @param id
	 */
	void setId(int id) {
		this.id = id;
	}

	public int id() {
		return id;
	}

	/**
	 * Computes the hash code to be returned by hashCode(). This is run the
	 * first time hashCode is run. The hash is cached for future calls to
	 * hashCode();
	 * 
	 * @return hash code
	 */
	protected abstract int computeHashCode();

	@Override
	public int hashCode() {
		if (id == NOT_HASHED) {
			hashCode = computeHashCode();
			id = HASHED;
		}
		return hashCode;
	}

	/**
	 * Is the given symbolic object equal to this one---assuming the given
	 * symbolic object is of the same kind as this one? Must be defined in any
	 * concrete subclass.
	 * 
	 * @param that
	 *            a symbolic object of the same kind as this one
	 * @return true iff they define the same type
	 */
	protected abstract boolean intrinsicEquals(SymbolicObject o);

	@Override
	public boolean equals(Object o) {
		if (this == o)
			return true;
		if (o instanceof CommonSymbolicObject) {
			CommonSymbolicObject that = (CommonSymbolicObject) o;

			if (this.symbolicObjectKind() != that.symbolicObjectKind())
				return false;
			if (id >= 0 && that.id >= 0) {
				return id == that.id;
			}
			if (id >= HASHED && that.id >= HASHED && hashCode != that.hashCode)
				return false;
			return intrinsicEquals(that);
		}
		return false;
	}

	/**
	 * Canonizes the children of this symbolic object. Replaces each child with
	 * the canonic version of that child.
	 * 
	 * @param factory
	 *            the object factory that is responsible for this symbolic
	 *            object
	 */
	public abstract void canonizeChildren(ObjectFactory factory);

	/**
	 * Places parentheses around the string buffer.
	 * 
	 * @param buffer
	 *            a string buffer
	 */
	protected void atomize(StringBuffer buffer) {
		buffer.insert(0, '(');
		buffer.append(')');
	}

	@Override
	public String toString() {
		if (debug)
			return toStringBufferLong().toString();
		else
			return toStringBuffer(false).toString();
	}

}
