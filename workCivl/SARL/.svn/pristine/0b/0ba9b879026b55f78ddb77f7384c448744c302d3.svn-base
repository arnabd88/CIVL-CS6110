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

import java.util.Comparator;

import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicIntegerType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicRealType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.expr.IF.NumericExpressionFactory;
import edu.udel.cis.vsl.sarl.ideal.common.NTMonic;
import edu.udel.cis.vsl.sarl.ideal.common.NTRationalExpression;
import edu.udel.cis.vsl.sarl.ideal.common.One;
import edu.udel.cis.vsl.sarl.util.KeySetFactory;

/**
 * <p>
 * An {@link IdealFactory} provides a few services beyond those guaranteed by an
 * arbitrary {@link NumericExpressionFactory}.
 * </p>
 * 
 * <p>
 * The ideal factory produces and manipulates the following kinds of numeric
 * expressions:
 * </p>
 * 
 * <p>
 * A {@link Constant} represents a concrete value. Each constant has either
 * integer or real type.
 * </p>
 * 
 * <p>
 * A {@link Primitive} expression is one which is not concrete and which is to
 * be treated as an atomic expression, such as a variable, from the point of
 * view of ideal mathematical arithmetic. Examples: symbolic constants, array
 * read expressions of integer or real type, tuple read expressions of integer
 * or real types, and function applications for functions returning integer or
 * real are all primitive expressions. In addition, in this factory a
 * {@link Polynomial} is a {@link Primitive} so that it can be treated as a
 * "variable" in an expression.
 * </p>
 * 
 * <p>
 * Any value which is the result of raising a primitive expression to a concrete
 * positive integer power is an instance of {@link PrimitivePower}. Any
 * {@link Primitive} is also a {@link PrimitivePower} by taking the exponent to
 * be 1.
 * </p>
 * 
 * <p>
 * A {@link Monic} is the product of {@link PrimitivePower}s. Any
 * {@link PrimitivePower} is also a {@link Monic}: it is the product of a single
 * primitive-power. The {@link Constant} 1 (integer or real) is also a
 * {@link Monic}: it is the empty product. The integer and real 1s are the only
 * constants which are also {@link Monic}s.
 * </p>
 * 
 * <p>
 * A {@link Monomial} is the product of a {@link Constant} and a {@link Monic}.
 * Any {@link Constant} is also a {@link Monomial} by taking 1 for the monic.
 * Any {@link Monic} is also a {@link Monomial} by taking 1 for the constant.
 * </p>
 * 
 * <p>
 * A <i>term map</i> is a map from {@link Monic} to {@link Monomial} with the
 * property that a monic <i>m</i> in the key set maps to a monomial of the form
 * <i>c</i>*<i>m</i> for some non-zero constant <i>c</i>. A term map is a
 * {@link SymbolicMap}, not a {@link SymbolicExpression}.
 * </p>
 * 
 * <p>
 * A {@link Polynomial} is a sum of the {@link Monomial} values of a term map.
 * {@link Polynomial} is also a sub-type of {@link Primitive}, which is a
 * subtype of {@link PrimitivePower}, which is a sub-type of {@link Monic},
 * which is a sub-type of {@link Monomial}. In this factory, each instance
 * <code>p</code> of {@link Polynomial} satisfies all of the following:
 * <ol>
 * <li><code>p</code> is the sum of at least 2 non-zero monomials</li>
 * <li>no term of <code>p</code> is a {@link Polynomial}</li>
 * <li>if <code>p</code> has integer type, the GCD of its coefficients is 1 and
 * the leading coefficient is positive</li>
 * <li>if <code>p</code> has real type, the leading coefficient is 1</li>
 * </ol>
 * </p>
 * 
 * <p>
 * The sum of two term maps is defined by combining the two maps by combining
 * two terms with the same monic by adding the coefficients. The product of two
 * term maps is defined in the usual way: by multiplying each element in one
 * with each element in the other, then combining terms with the same monic by
 * adding coefficients. The product of a {@link Constant} and a term map is
 * defined by multiplying that constant by each {@link Monomial} value in the
 * term map. The n-th power of a term map is the term map obtained by
 * multiplying the term map with itself n times.
 * </p>
 * 
 * <p>
 * Given any {@link Monomial} <i>m</i>, the <i>term map</i> of <i>m</i> is
 * defined as follows:
 * <ol>
 * <li>if <i>m</i> is a {@link Polynomial}, the term map is the term map of that
 * polynomial</li>
 * <li>if <i>m</i> is the product of a {@link Constant} and a {@link Polynomial}
 * , the term map is the product of the constant and the term map of the
 * polynomial</li>
 * <li>otherwise, the term map is the map with one entry with value <i>m</i>.
 * </li>
 * </ol>
 * </p>
 * 
 * <p>
 * The <i>expansion</i> of a {@link Monomial} <i>m</i> is the term map defined
 * recursively as follows:
 * <ul>
 * <li>If <i>m</i> is a {@link Primitive} which is not a {@link Polynomial}, the
 * expansion of <i>m</i> is the singleton map with value <i>m</i>.</li>
 * <li>If <i>m</i> is a {@link Polynomial}, the expansion of <i>m</i> is the sum
 * of the expansions of the terms of <i>m</i>.</li>
 * <li>The expansion of the product of a {@link Constant} and a {@link Monic} is
 * the product of the constant with the expansion of the {@link Monic}.</li>
 * <li>The expansion of a {@link PrimitivePower} <i>p</i> <sup><i>n</i></sup> is
 * the expansion of <i>p</i> raised to the <i>n<sup>th</sup></i> power.</li>
 * </ul>
 * </p>
 * 
 * <p>
 * In the following examples, suppose <i>X</i> and <i>Y</i> are
 * {@link Primitive}s which are not {@link Polynomial}s.
 * </p>
 * 
 * <ul>
 * <li>the expansion of the {@link Monomial} <i>X</i> is {<i>X</i> }</li>
 * <li>the expansion of the {@link Polynomial} <i>X</i>+<i>Y</i> is {<i>X</i>,
 * <i>Y</i>}</li>
 * <li>the expansion of the {@link Monomial} 2*(<i>X</i>+<i>Y</i>) is {2*
 * <i>X</i>, 2*<i>Y</i>}</li>
 * <li>the expansion of the {@link Polynomial} 2*(<i>X</i>+ <i>Y</i>) + <i>X</i>
 * is {3*<i>X</i>, <i>Y</i>}</li>
 * <li>the expansion of the {@link Monomial} <i>X</i><sup>2</sup> is {<i>X</i>
 * <sup>2</sup>}</li>
 * <li>the expansion of the {@link Monomial} (<i>X</i>+<i>Y</i>) <sup>2</sup> is
 * {<i>X</i><sup>2</sup>, 2*<i>XY</i>, <i>Y</i> <sup>2</sup></li>
 * </ul>
 * 
 * <p>
 * The product of two {@link Monomial}s is a {@link Monomial} and is defined in
 * the obvious way, by multiplying primitive powers.
 * </p>
 * 
 * <p>
 * Suppose <i>m</i><sub>1</sub> and <i>m</i><sub>2</sub> are two
 * {@link Monomial}s with no primitive factor in common. The sum <i>m</i>
 * <sub>1</sub> + <i>m</i><sub>2</sub> is defined as follows. First, there is
 * the option of using the ordinary term map or the expansion of the two
 * monomials. The choice of whether or not to expand can be made using some
 * heuristic. In any case, the two term maps are added. The resulting term map
 * is factored (if possible) to produce a {@link Monomial}; the result may be a
 * {@link Polynomial}.
 * </p>
 * 
 * <p>
 * The sum of two arbitrary {@link Monomial}s <i>m</i><sub>1</sub> and <i>m</i>
 * <sub>2</sub> is defined as follows. First, the greatest common factor is
 * factored out, so <i>m</i><sub>1</sub>=d*<i>r</i><sub>r</sub>, <i>m</i>
 * <sub>2</sub>=d*<i>r</i><sub>2</sub>, where <i>d</i> is a {@link Monomial} and
 * <i>r</i><sub>1</sub> and <i>r</i><sub>2</sub> are {@link Monomial}s which
 * have no primitive factor is common. Hence <i>m</i><sub>1</sub> + <i>m</i>
 * <sub>2</sub> = <i>d</i>*(<i>r</i><sub>1</sub>+<i>r</i><sub>2</sub>), where
 * the product is again monomial product and the sum <i>r</i><sub>1</sub>+
 * <i>r</i><sub>2</sub> is a {@link Monomial} computed as described above.
 * </p>
 * 
 * <p>
 * A {@link RationalExpression} is the quotient of two {@link Monomial}s. Any
 * {@link Monomial} is also a {@link RationalExpression} by taking the
 * denominator to be the (monomial) 1. Any {@link RationalExpression} of integer
 * type is also a {@link Monomial}. (The result of integer division of two
 * integer polynomials may be a {@link Primitive} expression with operator
 * {@link SymbolicOperator#INT_DIVIDE}.)
 * </p>
 * 
 * <p>
 * A relational numeric expression will always be in one of the following forms:
 * 
 * <ul>
 * <li><code>0&lt;m</code></li>
 * <li><code>0&le;m</code></li>
 * <li><code>m&lt;0</code></li>
 * <li><code>m&le;0</code></li>
 * <li><code>0=p</code></li>
 * <li><code>0&ne;p</code></li>
 * </ul>
 * 
 * where <code>m</code> is a {@link Monic} and <code>p</code> is a
 * {@link Primitive}.
 * </p>
 * 
 * <p>
 * Reductions: 0&lt;<i>x</i><sup>2</sup><i>y</i> iff 0&lt;<i>y</i>. Hence we can
 * assume all powers are 1. Furthermore 0&lt;<i>xy</i> iff ((0&lt;<i>x</i> &and;
 * 0&lt;<i>y</i>) &or; (0&lt;&minus;<i>x</i> &and; 0&lt;&minus;<i>y</i>)). This
 * can be used to reduce everything to {@link Primitive}s, but unfortunately the
 * size of the formula is exponential in the number of factors. A heuristic
 * could be used to determine whether to expand.
 * </p>
 * 
 * <p>
 * Equality and inequality reductions are easier because <i>xy</i>=0 iff (
 * <i>x</i>=0 &or; <i>y</i>=0), which does not involve an expansion in formula
 * size. Similarly, <i>xy</i>&ne;0 iff (<i>x</i>&ne;0 &and; <i>y</i>&ne;0).
 * </p>
 * 
 * @author siegel
 */
public interface IdealFactory extends NumericExpressionFactory {

	Monomial[] emptyTermList = new Monomial[0];

	PrimitivePower[] emptyPPList = new PrimitivePower[0];

	/**
	 * What is the purpose of the polynomial factory. Is it to create only
	 * non-trivial polynomials: expressions where operator is + and all
	 * arguments are instances of Monomial? Or is it to create all instances of
	 * Polynomial???
	 * 
	 * @return
	 */
	KeySetFactory<Monic, Monomial> polynomialFactory();

	KeySetFactory<Primitive, PrimitivePower> monicFactory();

	/**
	 * The {@link Comparator} on {@link Monic}s. This places some well-defined
	 * total order on the set of all instances of {@link Monic}.
	 * 
	 * @return the comparator on {@link Monic}s
	 */
	Comparator<Monic> monicComparator();

	/**
	 * Returns an {@link IntObject} wrapping the int 1.
	 * 
	 * @return the integer 1 as an {@link IntObject}
	 */
	IntObject oneIntObject();

	/**
	 * Returns an integer {@link Constant} wrapping a Java <code>int</code>
	 * value.
	 * 
	 * @param value
	 *            any Java <code>int</code>
	 * 
	 * @return the integer {@link Constant} wrapping the given
	 *         <code>value</code>
	 */
	Constant intConstant(int value);

	@Override
	/**
	 * Returns the integer constant zero (0).
	 * 
	 * @return the integer 0 represented as a {@link Constant}
	 */
	Constant zeroInt();

	@Override
	/**
	 * Returns the real constant zero (0.0).
	 * 
	 * @return the real number 0 represented as a {@link Constant}
	 */
	Constant zeroReal();

	/**
	 * Returns either the integer constant 0 or the real constant 0, according
	 * to the given <code>type</code>.
	 * 
	 * @param type
	 *            either a {@link SymbolicIntegerType} or a
	 *            {@link SymbolicRealType}
	 * 
	 * @return a value zero of the specified type
	 * @see #zeroInt()
	 * @see #zeroReal()
	 */
	Constant zero(SymbolicType type);

	/**
	 * Returns a {@link Constant} wrapping the given concrete {@link Number}.
	 * 
	 * @param number
	 *            any non-<code>null</code> {@link Number}
	 * 
	 * @return a {@link Constant} wrapping <code>number</code>
	 */
	Constant constant(Number number);

	/**
	 * Returns either the integer number one (1) or the real number 1 (1.0). The
	 * choice is made according to the given <code>type</code>. In either case,
	 * the object returned is an instance of both {@link Constant} and
	 * {@link Monic}, because one is the empty {@link Monic}.
	 * 
	 * @param type
	 *            either a {@link SymbolicIntegerType} or a
	 *            {@link SymbolicRealType}
	 * 
	 * @return the number 1 as a symbolic expression
	 */
	Constant one(SymbolicType type);

	// Primitive Powers...

	/**
	 * Returns an instance of {@link PrimitivePower} representing raising the
	 * given <code>primitive</code> the given <code>exponent</code>.
	 * 
	 * @param primitive
	 *            the base, a non-<code>null</code> numeric primitive of integer
	 *            or real type
	 * @param exponent
	 *            the exponent, which must be a non-negative integer
	 * @return a {@link PrimitivePower} expression representing raising
	 *         <code>primitive</code> to the power <code>exponent</code>
	 */
	PrimitivePower primitivePower(Primitive primitive, IntObject exponent);

	/**
	 * <p>
	 * Given the exponent in a potential power expression, this method computes
	 * a concrete integer that can be factored out of that exponent so that the
	 * exponent is in canonical form. Specifically, if the exponent has form
	 * p/q, and p=c*m, where p and q are {@link Monomial}s and c is a
	 * {@link Constant}, and c=n/d, where n and d are {@link IntegerNumber}s,
	 * this method returns n. Note that n may be positive or negative. It will
	 * only be 0 if <code>exponent</code> is 1.
	 * </p>
	 * 
	 * <p>
	 * The <code>exponent</code> can be safely divided by the integer returned
	 * by this method. If this method is given e and returns n, then the power
	 * expression can be rewritten as a {@link PrimitivePower} with primitive
	 * POWER(x,e/n) and exponent n, if n is positive, or as the rational
	 * expression 1/PrimitivePower[POWER(x,e/n), -n], if n is negative.
	 * </p>
	 * 
	 * @param exponent
	 *            a non-<code>null</code> rational expression of integer or real
	 *            type
	 * @return an concrete positive integer <code>n</code> which can be factored
	 *         out from <code>exponent</code>
	 */
	IntegerNumber getConcreteExponent(RationalExpression exponent);

	// Monics...

	/**
	 * Returns a (possibly trivial) monic as specified. If the given monic map
	 * is empty, this returns 1 (an instance of {@link One} of the appropriate
	 * type). If the monic map has a single entry, this returns the value for
	 * that entry, which is a {@link PrimitivePower}. Otherwise, returns a
	 * non-trivial monic (instance of {@link NTMonic}).
	 * 
	 * @see #ntMonic(SymbolicType, SymbolicMap)
	 * 
	 * @param type
	 *            either integer or real type
	 * @param factorSet
	 *            a monic map with any number of entries; this maps a primitive
	 *            to a power of that primitive; all keys and values must have
	 *            type consistent with <code>type</code>
	 * @return instance of {@link Monic} corresponding to arguments as described
	 *         above
	 */
	Monic monic(SymbolicType type, PrimitivePower[] factorSet);

	/**
	 * Given a {@link Monic} returns the {@link Monic} obtained by removing some
	 * of the {@link PrimitivePower} factors according to the given
	 * <code>mask</code>. The <code>mask</code> is an array whose length is the
	 * number of {@link PrimitivePower} factors in <code>monic</code>. A
	 * <code>true</code> mask entry indicates the corresponding factor should be
	 * kept; a <code>false</code> entry indicates the corresponding factor
	 * should be removed.
	 * 
	 * @param monic
	 *            a non-<code>null</code> {@link Monic}
	 * @param mask
	 *            array of boolean whose length equals number of primitive power
	 *            factors in <code>monic</code>
	 * @return a {@link Monic} with same type as <code>monic</code> obtained
	 *         from <code>monic</code> by keeping only those factors for which
	 *         the corresponding bit in <code>mask</code> is <code>true</code>
	 */
	Monic monicMask(Monic monic, boolean[] mask);

	BooleanExpression isZero(Monomial monomial);

	// Monomials...

	/**
	 * Returns a {@link Monomial} which is the product of the given
	 * <code>constant</code> and the given <code>monic</code>. The two arguments
	 * must have the same type. If <code>constant</code> is 1, the
	 * {@link Monomial} returned may be an instance of {@link Monic}; if
	 * <code>constant</code> is 0, the {@link Monomial} returned may be an
	 * instance of {@link Constant} (representing 0). This method relieves the
	 * use of having to figure out exactly which kind of object to create to
	 * represent the product of a {@link Constant} and a {@link Monic}.
	 * 
	 * @param constant
	 *            any non-<code>null</code> {@link Constant}
	 * @param monic
	 *            a {@link Monic} of the same type as the <code>constant</code>
	 * 
	 * @return the product of <code>constant</code> and <code>monic</code>
	 */
	Monomial monomial(Constant constant, Monic monic);

	/**
	 * Computes the product of any two {@link Monomial}s of the same type.
	 * 
	 * @param m1
	 *            a non-<code>null</code> {@link Monomial}
	 * @param m2
	 *            a non-<code>null</code> {@link Monomial} of the same type as
	 *            <code>m1</code>
	 * @return the product of <code>m1</code> and <code>m2</code>
	 */
	Monomial multiplyMonomials(Monomial m1, Monomial m2);

	/**
	 * Computes the sum of any two {@link Monomial}s of the same type.
	 * 
	 * @param m1
	 *            a non-<code>null</code> {@link Monomial}
	 * @param m2
	 *            a non-<code>null</code> {@link Monomial} of the same type as
	 *            <code>m1</code>
	 * @return the sum of <code>m1</code> and <code>m2</code>
	 */
	Monomial addMonomials(Monomial m1, Monomial m2);

	/**
	 * Computes the sum of a non-empty set of {@link Monomial}s of the same
	 * type. The result produced by this method may differ from that produced by
	 * repeated applications of the binary method
	 * {@link {@link #addMonomials(Monomial, Monomial)}. Example:
	 * 
	 * <pre>
	 *  (xy + x) + z = x(y+1) + z  // two binary additions
	 *   xy + x + z  = xy + x + z  // one invocation of this method
	 * </pre>
	 * 
	 * @param monomials
	 *            an array of positive length consisting of {@link Monomial}s
	 *            which all have the same type
	 * @return an expression representing the sum of the monomials
	 */
	Monomial addMonomials(Monomial[] monomials);

	/**
	 * Returns the product of a {@link Constant} and a {@link Monomial} of the
	 * same type.
	 * 
	 * @param constant
	 *            a non-<code>null</code> {@link Constant}
	 * @param monomial
	 *            a non-<code>null</code> {@link Monomial} of the same type as
	 *            <code>constant</code>
	 * @return a {@link Monomial} representing the product
	 */
	Monomial multiplyConstantMonomial(Constant constant, Monomial monomial);

	// Term maps...

	/**
	 * <p>
	 * Returns a {@link SymbolicMap} with a single entry mapping the monic
	 * {@link One} to itself. The type of {@link One} will be the given
	 * <code>type</code>.
	 * </p>
	 * 
	 * <p>
	 * A term map represents a set of {@link Monomial}s, which are considered to
	 * be the terms in a sum. The {@link Monomial}s are indexed by their
	 * corresponding {@link Monic}s for efficient look-up. An entry in a term
	 * map is an ordered pair of the form (<i>m,c*m</i>), where <i>m</i> is a
	 * {@link Monic} and <i>c</i> is a non-0 {@link Constant}.
	 * </p>
	 * 
	 * @param type
	 *            either a {@link SymbolicIntegerType} or a
	 *            {@link SymbolicRealType}
	 * @return the term map consisting of a single term, one
	 */
	Monomial[] oneTermMap(SymbolicType type);

	/**
	 * Computes the sum of two term maps as a term map. The sum is defined in
	 * the obvious way: the coefficient associated to a monic is the sum of the
	 * coefficients associated to that monic in the given maps, where the
	 * absence of a monic in a map is understood to be 0 (sparse
	 * representation). If the sum is 0, the entry is removed from the result,
	 * to maintain the sparse representation.
	 * 
	 * @see #oneTermMap(SymbolicType)
	 * @param map1
	 *            a non-<code>null</code> term map
	 * @param map2
	 *            a non-<code>null</code term map of the same type as <code>
	 *            map1</code>
	 * @return a term map which represents the sum of the two given maps
	 */
	Monomial[] addTermMaps(Monomial[] map1, Monomial[] map2);

	/**
	 * Returns the products of the two term maps as a term map. The product is
	 * roughly an O(n^2) operation, where n is the length of each term map. It
	 * is defined in the usual way: each term in the first map is multiplied
	 * with every term in the second map, and the results are summed.
	 * 
	 * @see #oneTermMap(SymbolicType)
	 * @param map1
	 *            a non-<code>null</code> term map
	 * @param map2
	 *            a non-<code>null</code term map of the same type as <code>
	 *            map1</code>
	 * @return a term map which represents the sum of the two given maps
	 */
	Monomial[] multiplyTermMaps(Monomial[] map1, Monomial[] map2);

	/**
	 * Computes the term map obtained by multiplying the given {@link Constant}
	 * with every term in a given term map.
	 * 
	 * @param constant
	 *            a non-<code>null</code> {@link Constant}
	 * @param map
	 *            a term map of the same type as <code>constant</code>
	 * @return the term map obtained by multiplying <code>constant</code> with
	 *         every term in <code>map</code>
	 */
	Monomial[] multiplyConstantTermMap(Constant constant, Monomial[] map);

	/**
	 * Raises a term map to the given power, returning the result as a term map.
	 * This is the same as multiplying the term map with itself
	 * <code>exponent</code> times. The <code>exponent</code> is a non-negative
	 * integer. The type must be provided in case <code>map</code> is empty.
	 * Otherwise, the <code>map</code> must have the type <code>type</code>.
	 * 
	 * @param type
	 *            the type of the given <code>map</code> and result
	 * @param map
	 *            a non-<code>null</code> term map
	 * @param exponent
	 *            a non-negative integer
	 * @return the result of multiplying <code>map</code> with itself
	 *         <code>exponent</code> times
	 */
	Monomial[] powerTermMap(SymbolicType type, Monomial[] map,
			IntObject exponent);

	/**
	 * <p>
	 * Computes a {@link Monomial} which is equivalent to the sum of the terms
	 * in the given term map. The goal is to attempt to factor the
	 * {@link Polynomial} as much as practical.
	 * </p>
	 * 
	 * <p>
	 * Pre-condition: <code>maps</code> is non-empty.
	 * </p>
	 * 
	 * @param terms
	 *            a term map, i.e., a map from {@link Monic} to {@link Monomial}
	 *            with the property that a {@link Monic} <i>m</i> maps to a
	 *            {@link Monomial} of the form <i>c</i>*<i>m</i>, for some non-0
	 *            {@link Constant} <i>c</i>
	 * @return a {@link Monomial} equivalent to the sum of the {@link Monomial}
	 *         values of <code>map</code>
	 */
	Monomial factorTermMap(Monomial[] terms);

	// Polynomials...

	/**
	 * Produces the result of summing the {@link Monomial}s of a term map as a
	 * {@link Polynomial}.
	 * 
	 * @param type
	 *            the type of <code>terms</code> (needed in case
	 *            <code>terms</code> is empty)
	 * @param terms
	 *            a non-<code>null</code> term map
	 * @return the result of summing the terms in the term map
	 */
	Polynomial polynomial(SymbolicType type, Monomial[] terms);

	// Rational Expressions...

	/**
	 * Constructs new instance of {@link NTRationalExpression}. Nothing is
	 * checked.
	 * 
	 * <p>
	 * Preconditions: numerator is not 0. If real type, denominator has degree
	 * at least 1 and leading coefficient 1. The numerator and denominator have
	 * no common factors in their factorizations.
	 * </p>
	 * 
	 * @param numerator
	 *            the polynomial to use as numerator
	 * @param denominator
	 *            the polynomial to use as denominator
	 * @return rational expression p/q
	 */
	RationalExpression ntRationalExpression(Monomial numerator,
			Monomial denominator);

	/**
	 * Given a rational expression <code>rational</code> returns an expression
	 * equivalent to 0&lt;<code>rational</code>. This method will perform basic
	 * simplifications; for example, if <code>rational</code> is concrete, this
	 * method will return a concrete boolean expression (either "true" or
	 * "false").
	 * 
	 * @param rational
	 *            a non-<code>null</code> instance of {@link RationalExpression}
	 * @return an expression equivalent to 0&lt;<code>rational</code>
	 */
	BooleanExpression isPositive(RationalExpression rational);

	/**
	 * Given a rational expression <code>rational</code> returns an expression
	 * equivalent to 0&le;<code>rational</code>. This method will perform basic
	 * simplifications; for example, if <code>rational</code> is concrete, this
	 * method will return a concrete boolean expression (either "true" or
	 * "false").
	 * 
	 * @param rational
	 *            a non-<code>null</code> instance of {@link RationalExpression}
	 * @return an expression equivalent to 0&le;<code>rational</code>
	 */
	BooleanExpression isNonnegative(RationalExpression rational);

	// General

	@Override
	RationalExpression power(NumericExpression arg0, NumericExpression arg1);

	@Override
	RationalExpression expression(SymbolicOperator operator,
			SymbolicType numericType, SymbolicObject... arguments);

	@Override
	RationalExpression add(NumericExpression arg0, NumericExpression arg1);

	@Override
	RationalExpression subtract(NumericExpression arg0, NumericExpression arg1);

	@Override
	RationalExpression multiply(NumericExpression arg0, NumericExpression arg1);

	@Override
	RationalExpression divide(NumericExpression arg0, NumericExpression arg1);

}
