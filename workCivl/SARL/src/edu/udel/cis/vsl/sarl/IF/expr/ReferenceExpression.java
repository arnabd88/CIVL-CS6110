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
package edu.udel.cis.vsl.sarl.IF.expr;

/**
 * <p>
 * An expression representing a way to reference into values. A reference
 * expression may be thought of as a function which accepts certain values
 * (represented as symbolic expressions) and for each such value, returns a
 * reference to some sub-structure of that value.
 * </p>
 * 
 * <p>
 * For example, the identity reference accepts a value and returns a reference
 * to the entire value. It is like the identity function. A non-trivial example
 * is the reference expression "element 17 of an array." Thought of as a
 * function, that reference accepts any value of array type and returns element
 * 17 of that value. There is also a tuple component reference, which is similar
 * to an array reference, though the index must be concrete for a tuple
 * component reference, while for an array reference the index can be specified
 * by any symbolic expression of integer type.
 * </p>
 * 
 * <p>
 * Reference expressions can be composed. For example, a reference expression
 * corresponding to "element 17 of component 2 of element 32 of an array of
 * tuples of arrays" may be formed.
 * </p>
 * 
 * @see ArrayElementReference
 * @see TupleComponentReference
 * @see OffsetReference
 * @see UnionMemberReference
 * 
 * @author siegel
 */
public interface ReferenceExpression extends SymbolicExpression {

	/**
	 * The different kinds of references.
	 * 
	 * @author siegel
	 */
	public enum ReferenceKind {
		/**
		 * The "null" reference. This is a reference value that can never be
		 * dereferenced. Similar to C's <code>NULL</code> pointer.
		 */
		NULL,
		/**
		 * The identity reference. This is the reference that when applied to
		 * any value v, returns a reference to v.
		 */
		IDENTITY,
		/**
		 * An array element of reference. A reference of this kind is an
		 * instance of {@link ArrayElementReference}. It includes a reference to
		 * the "parent" array and an index.
		 */
		ARRAY_ELEMENT,
		/**
		 * A tuple component reference. A reference of this kind is an instance
		 * of {@link TupleComponentReference}. It includes a reference to the
		 * "parent" tuple value and a concrete integer field index.
		 */
		TUPLE_COMPONENT,
		/**
		 * A union member reference. A reference of this kind is an instance of
		 * {@link UnionMemberReference}. It includes a reference to the "parent"
		 * union value and an integer member index.
		 */
		UNION_MEMBER,
		/**
		 * An offset reference. A reference of this kind is an instance of
		 * {@link OffsetReference}. It includes a reference to a "parent" value
		 * and an integer "offset".
		 */
		OFFSET
	}

	/**
	 * Gets the kind of this reference.
	 * 
	 * @return the kind of this reference
	 */
	ReferenceKind referenceKind();

	/**
	 * Is this the null reference?
	 * 
	 * @return <code>true</code> iff the kind of this reference is
	 *         {@link ReferenceKind#NULL}.
	 */
	boolean isNullReference();

	/**
	 * Is this the identity reference?
	 * 
	 * @return <code>true</code> iff the kind of this reference is
	 *         {@link ReferenceKind#IDENTITY}.
	 */
	boolean isIdentityReference();

	/**
	 * Is this an array element reference?
	 * 
	 * @return <code>true</code> iff the kind of this reference is
	 *         {@link ReferenceKind#ARRAY_ELEMENT}.
	 */
	boolean isArrayElementReference();

	/**
	 * Is this a tuple component reference?
	 * 
	 * @return <code>true</code> iff the kind of this reference is
	 *         {@link ReferenceKind#TUPLE_COMPONENT}.
	 */
	boolean isTupleComponentReference();

	/**
	 * Is this a union member reference?
	 * 
	 * @return <code>true</code> iff the kind of this reference is
	 *         {@link ReferenceKind#UNION_MEMBER}.
	 */
	boolean isUnionMemberReference();

	/**
	 * Is this an "offset reference"?
	 * 
	 * @return <code>true</code> iff the kind of this reference is
	 *         {@link ReferenceKind#OFFSET}.
	 */
	boolean isOffsetReference();
}
