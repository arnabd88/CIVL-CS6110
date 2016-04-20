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

import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
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
 * A non-trivial primitive power represents a {@link Primitive} expression
 * raised to some concrete integer exponent; the exponent is at least 2.
 * 
 * @author siegel
 */
public class NTPrimitivePower extends HomogeneousExpression<SymbolicObject>
		implements PrimitivePower {

	/**
	 * Print debugging information?
	 */
	public final static boolean debug = false;

	/**
	 * Where to send the debugging output.
	 */
	public final static PrintStream out = System.out;

	/**
	 * Cached result of {@link #expand(IdealFactory)}.
	 */
	private Monomial[] expansion = null;

	/**
	 * Cached result of {@link #monicFactors(IdealFactory)}.
	 */
	private PrimitivePower[] monicFactors = null;

	/**
	 * Cached result of {@link #termMap(IdealFactory)}.
	 */
	private Monomial[] termMap = null;

	/**
	 * Constructs new {@link NTPrimitivePower} with given primitive and
	 * exponent.
	 * 
	 * @param primitive
	 *            a non-<code>null</code> instance of {@link Primitive}
	 * @param exponent
	 *            an integer greater than or equal to 2 represented as an
	 *            {@link IntObject}
	 */
	protected NTPrimitivePower(Primitive primitive, IntObject exponent) {
		super(SymbolicOperator.POWER, primitive.type(),
				new SymbolicObject[] { primitive, exponent });
		assert exponent.getInt() >= 2;
	}

	/**
	 * Returns the primitive base of this expression.
	 * 
	 * @return the primitive base of this expression
	 */
	public Primitive primitive() {
		return (Primitive) argument(0);
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
	public Constant monomialConstant(IdealFactory factory) {
		return factory.one(type());
	}

	@Override
	public Monic monic(IdealFactory factory) {
		return this;
	}

	@Override
	public IntObject primitivePowerExponent(IdealFactory factory) {
		return exponent();
	}

	/**
	 * Returns the exponent in this power expression.
	 * 
	 * @return the exponent
	 */
	public IntObject exponent() {
		return (IntObject) argument(1);
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
	public Primitive primitive(IdealFactory factory) {
		return (Primitive) argument(0);
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
				IntObject exponent = exponent();
				int totalDegree;

				if (debug) {
					totalDegree = totalDegree();
					out.println(
							"Starting: expanding primitive power of total degree "
									+ totalDegree + " with exponent "
									+ exponent);
					out.flush();
				}

				Primitive primitive = primitive();
				Monomial[] expandedPrimitive = primitive.expand(factory);

				expansion = factory.powerTermMap(type(), expandedPrimitive,
						exponent);
				if (debug) {
					out.println(
							"Finished: expanding primitive power of total degree "
									+ totalDegree + " with exponent " + exponent
									+ ": result has size " + expansion.length);
					out.flush();
				}
				if (isCanonic())
					factory.objectFactory().canonize(expansion);
			}
		}
		return expansion;
	}

	@Override
	public String toString() {
		return primitive().atomString() + "^" + exponent();
	}

	@Override
	public int monomialDegree() {
		return exponent().getInt();
	}

	@Override
	public Monomial[] termMap(IdealFactory factory) {
		if (termMap == null) {
			termMap = new Monomial[] { this };
			if (isCanonic())
				factory.objectFactory().canonize(termMap);
		}
		return termMap;
	}

	/**
	 * {@inheritDoc}
	 * 
	 * <p>
	 * The total degree of a primitive power is the product of the total degree
	 * of the primitive and the exponent.
	 * </p>
	 */
	@Override
	public int totalDegree() {
		return exponent().getInt() * primitive().totalDegree();
	}

	@Override
	public boolean hasNontrivialExpansion(IdealFactory factory) {
		Primitive p = primitive();

		return p instanceof NTPolynomial || p.hasNontrivialExpansion(factory);
	}

	@Override
	public void canonizeChildren(ObjectFactory of) {
		super.canonizeChildren(of);
		if (termMap != null)
			of.canonize(termMap);
		if (expansion != null)
			of.canonize(expansion);
		if (monicFactors != null)
			of.canonize(monicFactors);
	}

	@Override
	public int monomialOrder(IdealFactory factory) {
		return ((Primitive) argument(0)).monomialOrder(factory);
	}

	@Override
	public Monomial[] lower(IdealFactory factory) {
		Monomial[] lowering;
		Primitive primitive = ((Primitive) argument(0));

		if (!(primitive instanceof Polynomial))
			lowering = termMap(factory);
		else {
			lowering = factory.powerTermMap(type(), primitive.termMap(factory),
					exponent());
			if (isCanonic())
				factory.objectFactory().canonize(lowering);
		}
		return lowering;
	}

	@Override
	public RationalExpression powerRational(IdealFactory factory,
			RationalExpression exponent) {
		int n = exponent().getInt();
		RationalExpression nRat;

		if (exponent.type().isInteger()) {
			nRat = factory.intConstant(n);
		} else {
			NumberFactory nf = factory.numberFactory();

			nRat = factory.constant(nf.integerToRational(nf.integer(n)));
		}

		RationalExpression newExponent = factory.multiply(nRat, exponent);

		return factory.power(primitive(), newExponent);
	}

	@Override
	public PrimitivePower powerInt(IdealFactory factory, int exponent) {
		return factory.primitivePower(primitive(), factory.objectFactory()
				.intObject(exponent().getInt() * exponent));
	}
}
