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
package edu.udel.cis.vsl.sarl.ideal.IF;

/**
 * A {@link Monomial} is the product of a constant and a {@link Monic}. The
 * constant is called the "constant factor" of the monomial; the monic is called
 * the "monic factor" of the monomial.
 * 
 * @author Stephen F. Siegel
 * 
 */
public interface Monomial extends RationalExpression {

	/**
	 * Returns the constant factor of this monomial.
	 * 
	 * @param factory
	 *            the ideal factory responsible for this monomial
	 * @return the constant factor of this monomial
	 */
	Constant monomialConstant(IdealFactory factory);

	/**
	 * Returns the monic factor of this monomial.
	 *
	 * @param factory
	 *            the ideal factory responsible for this monomial
	 * @return the monic factor of this monomial
	 */
	Monic monic(IdealFactory factory);

	/**
	 * Returns the degree of the monic where each factor is considered to have
	 * degree 1. For example, (X^2+Y^2)^3*Z^2 has monomial degree 5: it has two
	 * factors, one of degree 3 and one of degree 2.
	 * 
	 * @return the monomial degree with NO expansion
	 */
	int monomialDegree();

	/**
	 * The degree of this monomial if it were fully expanded to a polynomial in
	 * which the variables cannot be expressed as the sum, product, difference,
	 * or quotient of expressions. For example, (X^2+Y^2)^3*Z^2 has total degree
	 * 8.
	 * 
	 * @return total degree of this monomial after full expansion to a
	 *         polynomial
	 */
	int totalDegree();

	/**
	 * Returns the expansion of this monomial.
	 * 
	 * @see IdealFactory
	 * 
	 * @param factory
	 *            the ideal factory responsible for this monomial
	 * @return term map whose sum is equivalent to this but with no
	 *         {@link Polynomial}s.
	 */
	Monomial[] expand(IdealFactory factory);

	/**
	 * Determines whether or not this monomial has a non-trivial expansion. A
	 * trivial expansion is one consisting of exactly one term.
	 * 
	 * @param factory
	 *            the ideal factory responsible for this monomial
	 * @return <code>true</code> iff this monomial has a non-trivial expansion
	 */
	boolean hasNontrivialExpansion(IdealFactory factory);

	/**
	 * Returns the term map of this monomial.
	 * 
	 * @see IdealFactory
	 * 
	 * @param factory
	 *            the ideal factory responsible for this monomial
	 * @return a term map whose sum is equivalent to this monomial
	 */
	Monomial[] termMap(IdealFactory factory);

	/**
	 * Computes the "monomial order" of this {@link Monomial}. This is defined
	 * as follows:
	 * <ul>
	 * <li>the monomial order of a {@link Constant} is 0</li>
	 * <li>the monomial order of a {@link Primitive} which is not a
	 * {@link Polynomial} (a "true primitive") is also 0</li>
	 * <li>the monomial order of a {@link PrimitivePower} s the monomial order
	 * of its {@link Primitive}</li>
	 * <li>the monomial order of a {@link Monic} is the maximum of the monomial
	 * orders of its {@link PrimitivePower} factors</li>
	 * <li>the monomial order of a {@link Monomial} is the monomial order of its
	 * {@link Monic}</li>
	 * <li>the monomial order of a {@link Polynomial} which is not a
	 * {@link Monomial} is one more than the monomial orders of its
	 * {@link Monomial} terms.</li>
	 * </ul>
	 * 
	 * <p>
	 * Another interpretation: consider this symbolic expressions as a rooted
	 * tree. Along any path from the root to a leaf, count the number of "+"
	 * (addition) operators to occur. (Note that each {@link Polynomial}
	 * introduces a single addition operator whose argument is a set of terms.)
	 * The maximum plus-count (over all paths) is the monomial order.
	 * </p>
	 * 
	 * @param factory
	 *            the {@link IdealFactory} responsible for this {@link Monomial}
	 * @return the monomial order of this {@link Monomial}
	 */
	int monomialOrder(IdealFactory factory);

	/**
	 * <p>
	 * Computes a term map from performing a single outer-level expansion. This
	 * is in contrast with {@link #expand(IdealFactory)}, which performs a full
	 * expansion.
	 * </p>
	 * 
	 * <p>
	 * Suppose the monomial order of this {@link Monomial} is d. Then the
	 * {@link Monomial}s occurring in the returned map will have monomial order
	 * at most d-1. Furthermore, if this is a {@link Polynomial}, the
	 * {@link Monomials} occurring in the returned map will have monomial order
	 * at most d-2 (assuming d>=2).
	 * </p>
	 * 
	 * @param factory
	 *            the {@link IdealFactory} responsible for this {@link Monomial}
	 * @return a term map with lower monomial order.
	 */
	Monomial[] lower(IdealFactory factory);

	@Override
	Monomial powerInt(IdealFactory factory, int exponent);
}
