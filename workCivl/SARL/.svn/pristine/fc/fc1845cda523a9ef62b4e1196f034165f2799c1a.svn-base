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
package edu.udel.cis.vsl.sarl.ideal.common;

import java.io.PrintStream;

import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicIntegerType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicRealType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.expr.common.HomogeneousExpression;
import edu.udel.cis.vsl.sarl.ideal.IF.Constant;
import edu.udel.cis.vsl.sarl.ideal.IF.IdealFactory;
import edu.udel.cis.vsl.sarl.ideal.IF.Monic;
import edu.udel.cis.vsl.sarl.ideal.IF.Monomial;
import edu.udel.cis.vsl.sarl.ideal.IF.Polynomial;
import edu.udel.cis.vsl.sarl.ideal.IF.Primitive;
import edu.udel.cis.vsl.sarl.ideal.IF.PrimitivePower;
import edu.udel.cis.vsl.sarl.ideal.IF.RationalExpression;
import edu.udel.cis.vsl.sarl.object.IF.ObjectFactory;

/**
 * <p>
 * An {@link NTPolynomial} ("non-trivial polynomial") is the sum of at least 2
 * {@link Monomial}s with different underlying monics, e.g., 1+<i>x</i>
 * <sup>2</sup>, <i>x</i>+<i>y</i>, or <i>x</i>+<i>xy</i>.
 * </p>
 * 
 * <p>
 * The set of {@link Monomial} terms is represented as a {@link SymbolicMap}. A
 * key in this map is a {@link Monic} <i>m</i>. The value associated to <i>m</i>
 * is a {@link Monomial} of the form <i>c*m</i> for some non-zero
 * {@link Constant} <i>c</i>. This kind of map is called a <i>term map</i>. The
 * reason for using a map is to provide efficient look-up of terms using the
 * {@link Monic}.
 * </p>
 * 
 * @author siegel
 */
public class NTPolynomial extends HomogeneousExpression<Monomial>
		implements Polynomial {

	private final static Monomial[] emptyMonomialList = new Monomial[0];

	/**
	 * Print debugging info?
	 */
	public final static boolean debug = false;

	/**
	 * Where to send debugging info.
	 */
	public final static PrintStream out = System.out;

	/**
	 * The total degree of the polynomial, or -1 if the degree has not yet been
	 * computed.
	 */
	private int totalDegree = -1;

	/**
	 * Cached value returned by {@link #expand(IdealFactory)}.
	 */
	private Monomial[] expansion = null;

	/**
	 * Cached value returned by {@link #monicFactors(IdealFactory)}: a singleton
	 * map from this to this.
	 */
	private PrimitivePower[] monicFactors = null;

	/**
	 * Cached result for method {@link #hasNontrivialExpansion(IdealFactory)}.
	 * -1 means this has not yet been computed. 0 means false. 1 means true.
	 */
	byte hasNTE = -1;

	/**
	 * <p>
	 * Constructs new {@link NTPolynomial} wrapping the given term map. The
	 * <code>type</code> must equal the type of <code>termMap</code>. The caller
	 * provides is just for reasons of efficiency.
	 * </p>
	 * 
	 * Preconditions (not necessarily checked):
	 * <ul>
	 * <li><code>termMap</code> has at least 2 entries</li>
	 * <li>every key and value in <code>termMap</code> has type
	 * <code>type</code></li>
	 * <li>the {@link Monomial} value associated to a {@link Monic} key <i>m</i>
	 * has {@link Monic} equal to <i>m</i></li>
	 * </ul>
	 * 
	 * @param type
	 *            either {@link SymbolicRealType} or {@link SymbolicIntegerType}
	 * @param termMap
	 *            a term map with at least 2 entries
	 */
	protected NTPolynomial(SymbolicType type, Monomial[] termMap) {
		super(SymbolicOperator.ADD, type, termMap);
		assert termMap.length >= 2;
	}

	@Override
	public Monomial[] termMap(IdealFactory factory) {
		return arguments;
	}

	public Monomial[] termMap() {
		return arguments;
	}

	/**
	 * {@inheritDoc}
	 * 
	 * <p>
	 * Since the terms are ordered by decreasing degree, the first one should be
	 * the degree of this polynomial.
	 * </p>
	 * 
	 * @return the degree of this polynomial
	 */
	@Override
	public int polynomialDegree() {
		return arguments[0].monomialDegree();
	}

	@Override
	public Constant constantTerm(IdealFactory factory) {
		Monomial lastTerm = arguments[arguments.length - 1];

		return lastTerm instanceof Constant ? (Constant) lastTerm
				: factory.zero(type);
	}

	@Override
	public Monomial[] expand(IdealFactory factory) {
		if (expansion == null) {
			Monomial[] termMap = termMap();

			if (hasNontrivialExpansion(factory)) {
				if (debug) {
					out.println("Starting expansion of " + shortString());
					out.flush();
				}
				expansion = emptyMonomialList;
				for (Monomial oldTerm : arguments)
					expansion = factory.addTermMaps(expansion,
							oldTerm.expand(factory));
				if (isCanonic())
					factory.objectFactory().canonize(expansion);
				if (debug) {
					out.println("Finished expansion of " + shortString());
					out.flush();
				}
			} else {
				expansion = termMap;
			}
		}
		return expansion;
	}

	@Override
	public boolean hasNontrivialExpansion(IdealFactory factory) {
		if (hasNTE < 0) {
			hasNTE = 0;
			for (Monomial m : arguments) {
				if (m.hasNontrivialExpansion(factory)) {
					hasNTE = 1;
					break;
				}
			}
		}
		return hasNTE == 1;
	}

	/**
	 * {@inheritDoc}
	 * 
	 * <p>
	 * Gets the maximum of the total degrees of the terms. Note that the terms
	 * are sorted by decreasing monomial degrees (not total degrees), so we have
	 * to search over all terms. We might consider changing the order to use
	 * total degrees, in which case this method can just look at the first term.
	 * </p>
	 * 
	 */
	@Override
	public int totalDegree() {
		if (totalDegree < 0) {
			for (Monomial monomial : arguments) {
				int d = monomial.totalDegree();

				if (d > totalDegree)
					totalDegree = d;
			}
		}
		return totalDegree;
	}

	@Override
	public Primitive primitive(IdealFactory factory) {
		return this;
	}

	@Override
	public IntObject primitivePowerExponent(IdealFactory factory) {
		return factory.oneIntObject();
	}

	@Override
	public PrimitivePower[] monicFactors(IdealFactory factory) {
		if (monicFactors == null) {
			monicFactors = new PrimitivePower[] { this };
			if (isCanonic())
				factory.objectFactory().canonize(monicFactors);
		}
		return monicFactors;
	}

	@Override
	public boolean isTrivialMonic() {
		return false;
	}

	@Override
	public Constant monomialConstant(IdealFactory factory) {
		return factory.one(type());
	}

	@Override
	public Monic monic(IdealFactory factory) {
		return this;
	}

	@Override
	public int monomialDegree() {
		return 1;
	}

	@Override
	public Monomial numerator(IdealFactory factory) {
		return this;
	}

	@Override
	public Monomial denominator(IdealFactory factory) {
		return factory.one(type());
	}

	@Override
	public void canonizeChildren(ObjectFactory of) {
		super.canonizeChildren(of);
		if (expansion != null)
			of.canonize(expansion);
		if (monicFactors != null)
			of.canonize(monicFactors);
	}

	public String shortString() {
		return "Poly[id=" + id() + ",numTerms=" + arguments.length
				+ ",totalDegree=" + totalDegree() + "]";
	}

	@Override
	public int monomialOrder(IdealFactory factory) {
		int monomialOrder = 0;
		for (Monomial monomial : arguments) {
			int mo = monomial.monomialOrder(factory);

			if (mo > monomialOrder)
				monomialOrder = mo;
		}
		monomialOrder++;
		return monomialOrder;
	}

	@Override
	public Monomial[] lower(IdealFactory factory) {
		Monomial[] lowering = null;
		int order = monomialOrder(factory);
		Monomial[] termMap = termMap();

		if (order > 1) {
			lowering = emptyMonomialList;
			for (Monomial oldTerm : arguments)
				lowering = factory.addTermMaps(lowering,
						oldTerm instanceof Primitive ? oldTerm.termMap(factory)
								: oldTerm.lower(factory));
			if (isCanonic())
				factory.objectFactory().canonize(lowering);
		} else {
			lowering = termMap;
		}
		return lowering;
	}

	@Override
	public RationalExpression powerRational(IdealFactory factory,
			RationalExpression exponent) {
		return factory.expression(SymbolicOperator.POWER, type(), this,
				exponent);
	}

	@Override
	public PrimitivePower powerInt(IdealFactory factory, int exponent) {
		return factory.primitivePower(this,
				factory.objectFactory().intObject(exponent));
	}
}
