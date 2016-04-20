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

import edu.udel.cis.vsl.sarl.expr.common.HomogeneousExpression;
import edu.udel.cis.vsl.sarl.ideal.IF.IdealFactory;
import edu.udel.cis.vsl.sarl.ideal.IF.Monomial;
import edu.udel.cis.vsl.sarl.ideal.IF.RationalExpression;

/**
 * A nontrivial {@link RationalExpression}. It consists of a numerator and
 * denominator, both {@link Monomial}s. The denominator is not 1 or 0, the
 * numerator is not 0, and the numerator does not equal the denominator.
 * 
 * @author siegel
 */
public class NTRationalExpression extends HomogeneousExpression<Monomial>
		implements RationalExpression {

	/**
	 * Constructs new {@link NRationalExpression} from given numerator and
	 * denominator.
	 * 
	 * <p>
	 * Preconditions (not necessarily checked):
	 * <ul>
	 * <li>denominator is not 1 or 0</li>
	 * <li>numerator is not 0</li>
	 * <li>numerator and denominator have same type</li>
	 * <li>numerator is not equal to denominator</li>
	 * </ul>
	 * </p>
	 * 
	 * @param numerator
	 *            the numerator in the new rational expression
	 * @param denominator
	 *            the denominator in the new rational expression
	 */
	protected NTRationalExpression(Monomial numerator, Monomial denominator) {
		super(SymbolicOperator.DIVIDE, numerator.type(),
				new Monomial[] { numerator, denominator });
		assert !denominator.isOne();
		assert !denominator.isZero();
		assert !numerator.isZero();
		assert !numerator.equals(denominator);
	}

	public Monomial numerator(IdealFactory factory) {
		return argument(0);
	}

	/**
	 * Returns the numerator of this rational expression.
	 * 
	 * @return the numerator
	 */
	public Monomial numerator() {
		return argument(0);
	}

	public Monomial denominator(IdealFactory factory) {
		return argument(1);
	}

	/**
	 * Returns the denominator of this ratioal expression.
	 * 
	 * @return the denominator
	 */
	public Monomial denominator() {
		return argument(1);
	}

	@Override
	public RationalExpression powerRational(IdealFactory factory,
			RationalExpression exponent) {
		Monomial num = argument(0), den = argument(1);

		return factory.divide(num.powerRational(factory, exponent),
				den.powerRational(factory, exponent));
	}

	@Override
	public RationalExpression powerInt(IdealFactory factory, int n) {
		return factory.ntRationalExpression(numerator().powerInt(factory, n),
				denominator().powerInt(factory, n));
	}
}
