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

import edu.udel.cis.vsl.sarl.IF.object.IntObject;
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
 * A numeric primitive expression---one which is to be considered as an atomic
 * "variable" when used in other numeric expressions. Other classes may want to
 * extend this. Examples: symbolic constant, array read, tuple read, function
 * application, when those have numeric type.
 * 
 * @author siegel
 */
public class NumericPrimitive extends HomogeneousExpression<SymbolicObject>
		implements Primitive {

	/**
	 * Cache of value returned by {@link #monicFactors(IdealFactory)}. Singleton
	 * map from this to this, cached.
	 */
	private PrimitivePower[] monicFactors = null;

	/**
	 * Cache of value returned by {@link #termMap(IdealFactory)}.
	 */
	private Monomial[] termMap = null;

	public NumericPrimitive(SymbolicOperator operator, SymbolicType type,
			SymbolicObject... arguments) {
		super(operator, type, arguments);
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
	public Primitive primitive(IdealFactory factory) {
		return this;
	}

	@Override
	public IntObject primitivePowerExponent(IdealFactory factory) {
		return factory.oneIntObject();
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
	public int monomialDegree() {
		return 1;
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

	@Override
	public Monomial[] expand(IdealFactory factory) {
		return termMap(factory);
	}

	@Override
	public int totalDegree() {
		return 1;
	}

	@Override
	public boolean hasNontrivialExpansion(IdealFactory factory) {
		return false;
	}

	@Override
	public void canonizeChildren(ObjectFactory of) {
		super.canonizeChildren(of);
		if (termMap != null)
			of.canonize(termMap);
		if (monicFactors != null)
			of.canonize(monicFactors);
	}

	@Override
	public int monomialOrder(IdealFactory factory) {
		return 0;
	}

	@Override
	public Monomial[] lower(IdealFactory factory) {
		return termMap(factory);
	}

	@Override
	public RationalExpression powerRational(IdealFactory factory,
			RationalExpression exponent) {
		if (operator() == SymbolicOperator.POWER) {
			RationalExpression b = (RationalExpression) argument(0);
			RationalExpression e = (RationalExpression) argument(1);

			// (b^e)^exponent = b^(e*exponent)
			return factory.power(b, factory.multiply(e, exponent));
		}
		return factory.expression(SymbolicOperator.POWER, type(), this,
				exponent);
	}

	@Override
	public PrimitivePower powerInt(IdealFactory factory, int exponent) {
		// what if this is a POWER operation? no difference, simplifier
		// will simplify if needed
		return factory.primitivePower(this,
				factory.objectFactory().intObject(exponent));
	}
}
