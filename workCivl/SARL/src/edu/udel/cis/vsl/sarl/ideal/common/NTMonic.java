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

import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.expr.common.HomogeneousExpression;
import edu.udel.cis.vsl.sarl.ideal.IF.Constant;
import edu.udel.cis.vsl.sarl.ideal.IF.IdealFactory;
import edu.udel.cis.vsl.sarl.ideal.IF.Monic;
import edu.udel.cis.vsl.sarl.ideal.IF.Monomial;
import edu.udel.cis.vsl.sarl.ideal.IF.Primitive;
import edu.udel.cis.vsl.sarl.ideal.IF.PrimitivePower;
import edu.udel.cis.vsl.sarl.ideal.IF.RationalExpression;
import edu.udel.cis.vsl.sarl.object.IF.ObjectFactory;

/**
 * <p>
 * A non-trivial monic ("NTMonic") is the product of at least two
 * {@link PrimitivePower}s. The set of primitive powers comprising this product
 * is represented as a {@link SymbolicMap}.
 * </p>
 * 
 * <p>
 * A key in the map is a {@link Primitive} <i>p</i>. The value associated to
 * <i>p</i> is a {@link PrimitivePower} <i>p<sup>n</sup></i> for some <i>n</i>
 * &ge;1.
 * </p>
 * 
 * @author siegel
 * 
 */
public class NTMonic extends HomogeneousExpression<PrimitivePower>
		implements Monic {

	/**
	 * Print debugging output?
	 */
	public final static boolean debug = false;

	/**
	 * The stream to which debugging output should be sent.
	 */
	public final static PrintStream out = System.out;

	/**
	 * Cached value returned by method {@link #degree()}. Initial value is -1,
	 * indicating the method has not yet been called.
	 */
	private int monomialDegree = -1;

	/**
	 * Cached value returned by method {@link #totalDegree()}. Initial value is
	 * -1, indicating the method has not yet been called.
	 */
	private int totalDegree = -1;

	/**
	 * Cached result for method {@link #hasNontrivialExpansion(IdealFactory)}.
	 * -1 means this has not yet been computed. 0 means false. 1 means true.
	 */
	byte hasNTE = -1;

	/**
	 * Cached result of {@link #expand(IdealFactory)}.
	 */
	private Monomial[] expansion = null;

	/**
	 * Cached result of {@link #termMap(IdealFactory)}.
	 */
	private Monomial[] termMap = null;

	protected NTMonic(SymbolicType type, PrimitivePower[] factorMap) {
		super(SymbolicOperator.MULTIPLY, type, factorMap);
		assert factorMap.length >= 2;
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
	public PrimitivePower[] monicFactors(IdealFactory factory) {
		return arguments;
	}

	public PrimitivePower[] monicFactors() {
		return arguments;
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
	public boolean isTrivialMonic() {
		return false;
	}

	@Override
	public Monomial[] expand(IdealFactory factory) {
		if (expansion == null) {
			if (!hasNontrivialExpansion(factory)) {
				expansion = termMap(factory);
			} else {
				PrimitivePower[] factors = monicFactors();
				int totalDegree, numFactors;

				if (debug) {
					totalDegree = totalDegree();
					numFactors = factors.length;
					out.println("Starting: expanding monic of total degree "
							+ totalDegree + " with " + numFactors + " factors");
					// out.println("monic: " + this);
					out.flush();
				}
				expansion = factory.oneTermMap(type());
				for (PrimitivePower ppower : factors)
					expansion = factory.multiplyTermMaps(expansion,
							ppower.expand(factory));
				if (debug) {
					out.println("Finished: expanding monic of total degree "
							+ totalDegree + " with " + numFactors
							+ " factors: result has size " + expansion.length);
					out.flush();
				}
				if (isCanonic())
					factory.objectFactory().canonize(expansion);
			}
		}
		return expansion;
	}

	@Override
	public int monomialDegree() {
		if (monomialDegree < 0) {
			monomialDegree = 0;
			for (PrimitivePower expr : monicFactors())
				monomialDegree += expr.monomialDegree();
		}
		return monomialDegree;
	}

	@Override
	public int totalDegree() {
		if (totalDegree < 0) {
			totalDegree = 0;
			for (PrimitivePower expr : monicFactors())
				totalDegree += expr.totalDegree();
		}
		return totalDegree;
	}

	@Override
	public Monomial[] termMap(IdealFactory factory) {
		if (termMap == null) {
			termMap = new Monomial[] { this };
		}
		return termMap;
	}

	@Override
	public boolean hasNontrivialExpansion(IdealFactory factory) {
		if (hasNTE < 0) {
			hasNTE = 0;
			for (PrimitivePower pp : arguments) {
				Primitive p = pp.primitive(factory);

				if (p instanceof NTPolynomial
						|| p.hasNontrivialExpansion(factory)) {
					hasNTE = 1;
					break;
				}
			}
		}
		return hasNTE == 1;
	}

	@Override
	public void canonizeChildren(ObjectFactory of) {
		super.canonizeChildren(of);
		if (expansion != null)
			of.canonize(expansion);
		if (termMap != null)
			of.canonize(termMap);
		// if (lowering != null && !lowering.isCanonic())
		// lowering = of.canonic(lowering);
	}

	@Override
	public int monomialOrder(IdealFactory factory) {
		// if (monomialOrder < 0) {
		int monomialOrder = 0;
		// for ()
		for (SymbolicObject arg : arguments) {
			Primitive p = ((PrimitivePower) arg).primitive(factory);
			int po = p.monomialOrder(factory);

			if (po > monomialOrder)
				monomialOrder = po;
		}
		// }
		return monomialOrder;
	}

	@Override
	public Monomial[] lower(IdealFactory factory) {
		// if (lowering == null) {
		Monomial[] lowering = null;
		int order = monomialOrder(factory);

		if (order == 0) {
			lowering = termMap(factory);
		} else {
			PrimitivePower[] factors = monicFactors();

			lowering = factory.oneTermMap(type());
			for (PrimitivePower ppower : factors)
				lowering = factory.multiplyTermMaps(lowering,
						ppower instanceof Primitive ? ppower.termMap(factory)
								: ppower.lower(factory));
			if (isCanonic())
				factory.objectFactory().canonize(lowering);
		}
		// }
		return lowering;
	}

	@Override
	public RationalExpression powerRational(IdealFactory factory,
			RationalExpression exponent) {
		RationalExpression result = factory.one(type());

		for (PrimitivePower pp : monicFactors()) {
			result = factory.multiply(result,
					pp.powerRational(factory, exponent));
		}
		return result;
	}

	@Override
	public Monic powerInt(IdealFactory factory, int exponent) {
		PrimitivePower[] factors = monicFactors();
		int n = factors.length;
		PrimitivePower[] newFactors = new PrimitivePower[n];

		for (int i = 0; i < n; i++) {
			newFactors[i] = factors[i].powerInt(factory, exponent);
		}
		return factory.monic(type(), newFactors);
	}
}
