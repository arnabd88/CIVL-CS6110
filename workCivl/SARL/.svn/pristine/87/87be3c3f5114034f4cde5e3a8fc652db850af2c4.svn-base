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

import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.IF.number.RationalNumber;
import edu.udel.cis.vsl.sarl.IF.object.NumberObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicIntegerType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicRealType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.expr.common.HomogeneousExpression;
import edu.udel.cis.vsl.sarl.ideal.IF.Constant;
import edu.udel.cis.vsl.sarl.ideal.IF.IdealFactory;
import edu.udel.cis.vsl.sarl.ideal.IF.Monic;
import edu.udel.cis.vsl.sarl.ideal.IF.Monomial;
import edu.udel.cis.vsl.sarl.ideal.IF.RationalExpression;

/**
 * A constant which is not 1.
 * 
 * @author siegel
 * 
 */
public class NTConstant extends HomogeneousExpression<SymbolicObject> implements
		Constant {

	/**
	 * Constructs new {@link NTConstant} of given type, wrapping given numeric
	 * value.
	 * 
	 * @param type
	 *            either a {@link SymbolicRealType} or
	 *            {@link SymbolicIntegerType}
	 * @param value
	 *            the numeric value to be wrapped; its type must be consistent
	 *            with <code>type</code>
	 */
	protected NTConstant(SymbolicType type, NumberObject value) {
		super(SymbolicOperator.CONCRETE, type, new SymbolicObject[] { value });
		assert !value.isOne();
	}

	public NumberObject value() {
		return (NumberObject) argument(0);
	}

	public Number number() {
		return value().getNumber();
	}

	public boolean isZero() {
		return value().isZero();
	}

	public boolean isOne() {
		return false;
	}

	@Override
	public Constant monomialConstant(IdealFactory factory) {
		return this;
	}

	@Override
	public Monic monic(IdealFactory factory) {
		return (Monic) factory.one(type());
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
	public Monomial[] termMap(IdealFactory factory) {
		return isZero() ? IdealFactory.emptyTermList : new Monomial[] { this };
	}

	@Override
	public int monomialDegree() {
		return isZero() ? -1 : 0;
	}

	@Override
	public Monomial[] expand(IdealFactory factory) {
		return termMap(factory);
	}

	@Override
	public int totalDegree() {
		return isZero() ? -1 : 0;
	}

	@Override
	public boolean hasNontrivialExpansion(IdealFactory factory) {
		return false;
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
		NumberFactory numFactory = factory.numberFactory();
		RationalNumber exp = (RationalNumber) factory.extractNumber(exponent);
		RationalNumber base = (RationalNumber) number();
		IntegerNumber exp_num = numFactory.integer(exp.numerator());
		IntegerNumber exp_den = numFactory.integer(exp.denominator());
		IntegerNumber base_num = numFactory.integer(base.numerator());
		IntegerNumber base_den = numFactory.integer(base.denominator());
		IntegerNumber result_num = null;
		IntegerNumber result_den = null;
		IntegerNumber tmp_num = null;
		IntegerNumber tmp_den = null;

		if (exp_num.signum() < 0) {
			IntegerNumber tmp = base_den;

			exp_num = numFactory.negate(exp_num);
			if (base_num.signum() < 0) {
				base_den = numFactory.negate(base_num);
				base_num = numFactory.negate(tmp);
			} else {
				base_den = base_num;
				base_num = tmp;
			}

		}
		assert exp_num.signum() >= 0;
		result_num = numFactory.power(base_num, exp_num);
		result_den = numFactory.power(base_den, exp_num);
		tmp_num = numFactory.nthRootInt(result_num, exp_den);
		tmp_den = numFactory.nthRootInt(result_den, exp_den);
		if (tmp_num == null || tmp_den == null) {
			return factory.expression(SymbolicOperator.POWER, type(), this,
					exponent);
		} else {
			return factory.constant(numFactory.fraction(tmp_num, tmp_den));
		}
	}

	@Override
	public Constant powerInt(IdealFactory factory, int n) {
		Number baseValue = number();
		SymbolicType type = type();
		Number result = factory.one(type).number();
		NumberFactory nf = factory.numberFactory();

		assert n >= 0;
		if (n > 0) {
			while (true) {
				if (n % 2 != 0) {
					result = nf.multiply(result, baseValue);
					n -= 1;
					if (n == 0)
						break;
				}
				baseValue = nf.multiply(baseValue, baseValue);
				n /= 2;
			}
		}
		return factory.constant(result);
	}
}
