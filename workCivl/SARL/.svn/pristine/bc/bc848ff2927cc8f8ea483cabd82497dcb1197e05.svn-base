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
package edu.udel.cis.vsl.sarl.ideal.simplify;

import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.IF.number.RationalNumber;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.ideal.IF.Constant;
import edu.udel.cis.vsl.sarl.ideal.IF.IdealFactory;
import edu.udel.cis.vsl.sarl.ideal.IF.Monic;
import edu.udel.cis.vsl.sarl.ideal.IF.Monomial;
import edu.udel.cis.vsl.sarl.ideal.IF.Polynomial;
import edu.udel.cis.vsl.sarl.type.IF.SymbolicTypeFactory;

public class AffineFactory {

	private IdealFactory idealFactory;

	private NumberFactory numberFactory;

	private SymbolicTypeFactory typeFactory;

	private IntegerNumber ZERO_INT, ONE_INT;

	private RationalNumber ZERO_REAL, ONE_REAL;

	private SymbolicType integerType, realType;

	public AffineFactory(IdealFactory idealFactory) {
		this.idealFactory = idealFactory;
		this.numberFactory = idealFactory.numberFactory();
		this.typeFactory = idealFactory.typeFactory();
		ZERO_INT = numberFactory.zeroInteger();
		ZERO_REAL = numberFactory.zeroRational();
		ONE_INT = numberFactory.oneInteger();
		ONE_REAL = numberFactory.oneRational();
		integerType = typeFactory.integerType();
		realType = typeFactory.realType();
	}

	public AffineExpression affine(Monic pseudo, Number coefficient,
			Number offset) {
		SymbolicType type = coefficient instanceof IntegerNumber ? integerType
				: realType;

		assert type.isInteger() && offset instanceof IntegerNumber
				|| type.isReal() && offset instanceof RationalNumber;
		return new AffineExpression(pseudo, coefficient, offset);
	}

	/**
	 * Computes a representation of the given {@link Polynomial} as an
	 * {@link AffineExpression} aX+b, where X is in pseudo form.
	 * 
	 * Also guarantees that if a=1 and b=0, the pseudo X will ==
	 * <code>poly</code> (not just .equals). This provides an easy way to
	 * determine whether the affine expression is "trivial".
	 */
	public AffineExpression affine(Polynomial poly) {
		SymbolicType type = poly.type();
		int degree = poly.polynomialDegree();

		// any instance of Polynomial has nonnegative degree.
		// The termmap must be non-empty.
		if (degree == 0) { // fp is constant
			return affine(null, type.isInteger() ? ZERO_INT : ZERO_REAL,
					((Constant) poly).number());
		} else {
			// first, subtract off constant term (if it is non-0).
			// then factor out best you can:
			// if real: factor out leading coefficient (unless it is 1)
			// if int: take gcd of coefficients and factor that out (unless it
			// is 1)
			Number constantTerm = poly.constantTerm(idealFactory).number();
			Number coefficient;
			Monic pseudo;

			if (constantTerm.isZero()) {
				// the polynomial is already normal, so nothing to do
				coefficient = type.isInteger() ? ONE_INT : ONE_REAL;
				pseudo = poly;
			} else {
				// better: one must be last, so remove last element
				// note: after removing one, resulting map might
				// have one entry
				Monomial difference = idealFactory
						.factorTermMap(idealFactory.polynomialFactory()
								.removeKey(poly.termMap(idealFactory),
										(Monic) idealFactory.one(type)));

				pseudo = difference.monic(idealFactory);
				coefficient = difference.monomialConstant(idealFactory)
						.number();
			}
			return affine(pseudo, coefficient, constantTerm);
		}
	}

	/**
	 * Determines a bound on the pseudo primitive polynomial X, assuming the
	 * predicate aX+b OP 0 holds, where OP is one of <,<=,>,>=.
	 * 
	 * The bound will be either an upper or a lower bound, depending upon the
	 * sign of a and the operator. If a>0, it is a lower bound. If a<0 it is an
	 * upper bound.
	 * 
	 * The bound returned will be either strict or not strict. If X is real (not
	 * integral) then the bound is strict iff the argument strict is true. If x
	 * is integral, the returned bound is always non-strict.
	 * 
	 * If a=0, this is null.
	 * 
	 * If a!=0 and X is real (not integral), this is -b/a. The argument strict
	 * is not used in this case.
	 * 
	 * If X is integral, there are 4 cases to consider. The first factor is the
	 * sign of a, the second is the argument strict.
	 * 
	 * Suppose a<0, so we are dealing with an upper bound c=-b/a.
	 * 
	 * If strict is true, we have, X<c, which is equivalent to X<=ceil(c)-1.
	 * 
	 * If strict is false, we have X<=c, which is equivalent to X<=floor(c).
	 * 
	 * Suppose a>0, so we are dealing with a lower bound c=-b/a.
	 * 
	 * If strict is true, we have X>c, i.e. X>=floor(c)+1.
	 * 
	 * If strict is false, we have X>=c, i.e., X>=ceil(c).
	 * 
	 * All of the previous is for the case X>0 or X>=0. If X<0 or X<=0 is the
	 * inequality, the following changes are made. If a>0, it is an upper bound;
	 * if a<0 it is a lower bound.
	 * 
	 * For the integral cases:
	 * 
	 * Suppose a<0, so lower bound.
	 * 
	 * If strict is true, X>c, i.e., X>=floor(c)+1.
	 * 
	 * If strict is false, X>=c, i.e., X>=ceil(c)
	 * 
	 * Suppose a>0, so upper bound.
	 * 
	 * If strict is true, X<c, i.e., X<=ceil(c)-1
	 * 
	 * If strict is false, X<=c, i.e., X<=floor(c).
	 * 
	 * (a<0 && gt) || (a>0 && !gt) -> floor(c)+1
	 * 
	 * Etc.
	 * 
	 */
	public Number bound(AffineExpression affine, boolean gt, boolean strict) {
		RationalNumber rationalBound = null;
		Number result = null;
		Monic pseudo = affine.pseudo();
		RationalNumber offset = numberFactory.rational(affine.offset());
		RationalNumber coefficient = numberFactory
				.rational(affine.coefficient());

		if (pseudo != null) {
			rationalBound = numberFactory
					.negate(numberFactory.divide(offset, coefficient));
			if (pseudo.type().isInteger()) {
				boolean pos = coefficient.signum() >= 0;

				if ((pos && gt) || (!pos && !gt)) {
					if (strict)
						result = numberFactory.add(ONE_INT,
								numberFactory.floor(rationalBound));
					else
						result = numberFactory.ceil(rationalBound);
				} else {
					if (strict)
						result = numberFactory.subtract(
								numberFactory.ceil(rationalBound), ONE_INT);
					else
						result = numberFactory.floor(rationalBound);
				}
			} else {
				result = rationalBound;
			}
		}
		return result;
	}

	/**
	 * Given a value for the "pseudo" X, returns the value of the affine
	 * expressions aX+b.
	 * 
	 * @param affine
	 *            the affine expression aX+b
	 * @param pseudoValue
	 *            a concrete value for X
	 * @return the concrete value obtained by substituting
	 *         <code>pseudoValue</code> for X in aX+b
	 */
	public Number affineValue(AffineExpression affine, Number pseudoValue) {
		if (affine.pseudo() == null)
			return affine.offset();
		return numberFactory.add(
				numberFactory.multiply(affine.coefficient(), pseudoValue),
				affine.offset());
	}

}
