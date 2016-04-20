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
package edu.udel.cis.vsl.sarl.number.real;

import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Interval;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.number.RationalNumber;

/**
 * Immutable implementation of {@link Interval}.
 */
public class CommonInterval implements Interval {
	// TODO: add Java-doc for fields, constructors and functions.

	// Constants ...

	public final static Number POS_INFINITY = null;

	public final static Number NEG_INFINITY = null;

	// Private Fields ...

	private boolean isIntegral;

	private Number lower;

	private boolean strictLower;

	private Number upper;

	private boolean strictUpper;

	// Constructors ...
	// TODO: Java-doc should include pre-cond.
	public CommonInterval(boolean isIntegral, Number lower,
			boolean strictLower, Number upper, boolean strictUpper) {
		assert !isIntegral
				|| ((lower == NEG_INFINITY || lower instanceof IntegerNumber) && (upper == POS_INFINITY || upper instanceof IntegerNumber));
		assert !isIntegral || (lower == NEG_INFINITY && strictLower)
				|| (lower != NEG_INFINITY && !strictLower) || lower.isZero();
		assert !isIntegral || (upper == POS_INFINITY && strictUpper)
				|| (upper != POS_INFINITY && !strictUpper) || upper.isZero();
		assert isIntegral
				|| ((lower == NEG_INFINITY || lower instanceof RationalNumber) && (upper == POS_INFINITY || upper instanceof RationalNumber));
		assert isIntegral || lower != NEG_INFINITY || strictLower;
		assert isIntegral || upper != POS_INFINITY || strictUpper;

		int compare;

		// <a,b> with a>b is unacceptable
		// (0,0) is fine: the unique representation of the empty set
		// [a,a] is fine, but not (a,a), [a,a), or (a,a]
		assert lower == NEG_INFINITY
				|| upper == POS_INFINITY
				|| (compare = lower.numericalCompareTo(upper)) < 0
				|| (compare == 0 && ((!strictLower && !strictUpper) || (lower
						.isZero() && strictLower && strictUpper)));
		this.isIntegral = isIntegral;
		this.lower = lower;
		this.strictLower = strictLower;
		this.upper = upper;
		this.strictUpper = strictUpper;
	}

	// Methods specified by interface "Object"

	@Override
	public CommonInterval clone() {
		return new CommonInterval(isIntegral, lower, strictLower, upper,
				strictUpper);
	}

	@Override
	public boolean equals(Object object) {
		if (object instanceof CommonInterval) {
			CommonInterval that = (CommonInterval) object;

			if (isIntegral != that.isIntegral
					|| strictLower != that.strictLower
					|| strictUpper != that.strictUpper)
				return false;

			Number thatUpper = that.upper();

			if ((upper == null) != (thatUpper == null))
				return false;

			Number thatLower = that.lower();

			if ((lower == null) != (thatLower == null))
				return false;
			if (upper != null && !upper.equals(thatUpper))
				return false;
			if (lower != null && !lower.equals(thatLower))
				return false;
			return true;
		}
		return false;
	}

	@Override
	public String toString() {
		String result;

		result = strictLower ? "(" : "[";
		result += lower == null ? "-infty" : lower.toString();
		result += ",";
		result += upper == null ? "+infty" : upper.toString();
		result += strictUpper ? ")" : "]";
		return result;
	}

	// Methods specified by interface "Interval"

	@Override
	public Number lower() {
		return lower;
	}

	@Override
	public Number upper() {
		return upper;
	}

	@Override
	public boolean strictLower() {
		return strictLower;
	}

	@Override
	public boolean strictUpper() {
		return strictUpper;
	}

	@Override
	public boolean isIntegral() {
		return isIntegral;
	}

	@Override
	public boolean isReal() {
		return !isIntegral;
	}

	@Override
	public boolean isEmpty() {
		return strictLower && strictUpper && lower != null && upper != null
				&& lower.isZero() && upper.isZero();
	}

	@Override
	public boolean isUniversal() {
		return lower == null && upper == null;
	}

	@Override
	public boolean contains(Number number) {
		if (lower != null) {
			int compare = lower.numericalCompareTo(number);

			if (compare > 0 || (compare == 0 && strictLower))
				return false;
		}
		if (upper != null) {
			int compare = upper.numericalCompareTo(number);

			if (compare < 0 || (compare == 0 && strictUpper))
				return false;
		}
		return true;
	}

	@Override
	public int compare(Number number) {
		if (lower != null) {
			int compare = lower.numericalCompareTo(number);

			if (compare > 0 || (compare == 0 && strictLower))
				return 1;
		}
		if (upper != null) {
			int compare = upper.numericalCompareTo(number);

			if (compare < 0 || (compare == 0 && strictUpper))
				return -1;
		}
		return 0;
	}

	@Override
	public boolean isZero() {
		return lower != null && upper != null && lower.isZero()
				&& upper.isZero() && !strictLower;
	}
}
