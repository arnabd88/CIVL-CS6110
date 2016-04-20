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

import java.io.PrintWriter;
import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;

import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Interval;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.IF.number.RationalNumber;
import edu.udel.cis.vsl.sarl.util.BinaryOperator;

/**
 * An implementation of number factory based on infinite precision real
 * arithmetic.
 */
public class RealNumberFactory implements NumberFactory {

	// Fields: TODO: Add java-doc for fields
	/**
	 * Static variable for a number representing the positive infinity.
	 */
	private static Number POS_INFINITY = null;

	/**
	 * Static variable for a number representing the negative infinity.
	 */
	private static Number NEG_INFINITY = null;

	private static int LEFT_DISJOINTED = -3;
	private static int RIGHT_DISJOINTED = 3;
	private static int LEFT_INTERSECTED = -2;
	private static int RIGHT_INTERSECTED = 2;
	private static int CONTAINED_IN_INTERVAL1 = -1;
	private static int CONTAINED_IN_INTERVAL2 = 1;
	private static int EXACTLY_SAME = 0;

	private Map<BigInteger, RealInteger> integerMap = new HashMap<BigInteger, RealInteger>();

	private Map<RationalKey, RealRational> rationalMap = new HashMap<RationalKey, RealRational>();

	private RealInteger zeroInteger, oneInteger, tenInteger;

	private RealRational zeroRational, oneRational;

	private BinaryOperator<IntegerNumber> multiplier;

	private Exponentiator<IntegerNumber> exponentiator;

	/**
	 * The empty integer interval: (0,0).
	 */
	private Interval emptyIntegerInterval;

	/**
	 * The empty real interval: (0.0, 0.0).
	 */
	private Interval emptyRationalInterval;

	/**
	 * Uses a new factory to multiply two integer arguments.
	 */
	class IntMultiplier implements BinaryOperator<IntegerNumber> {
		private RealNumberFactory factory;

		IntMultiplier(RealNumberFactory factory) {
			this.factory = factory;
		}

		@Override
		public IntegerNumber apply(IntegerNumber arg0, IntegerNumber arg1) {
			return factory.multiply(arg0, arg1);
		}

	}

	public RealNumberFactory() {
		zeroInteger = integer(BigInteger.ZERO);
		oneInteger = integer(BigInteger.ONE);
		tenInteger = integer(BigInteger.TEN);
		zeroRational = fraction(zeroInteger, oneInteger);
		oneRational = fraction(oneInteger, oneInteger);
		multiplier = new IntMultiplier(this);
		emptyIntegerInterval = new CommonInterval(true, zeroInteger, true,
				zeroInteger, true);
		emptyRationalInterval = new CommonInterval(false, zeroRational, true,
				zeroRational, true);
	}

	@Override
	/**
	 * See interface javadoc. Returns absolute value of a Number.
	 * 
	 */
	public Number abs(Number number) {
		if (number.signum() < 0) {
			return negate(number);
		} else {
			return number;
		}
	}

	@Override
	/**
	 * See interface. This takes in a BigInteger, and returns an IntegerNumber.
	 * 
	 */
	public RealInteger integer(BigInteger big) {
		RealInteger oldValue = integerMap.get(big);

		if (oldValue != null) {
			return oldValue;
		} else {
			RealInteger newValue = new RealInteger(big);

			integerMap.put(big, newValue);
			return newValue;
		}
	}

	@Override
	/**
	 * Returns the BigInteger interpretation of a long.
	 */
	public RealInteger integer(long value) {
		return integer(BigInteger.valueOf(value));
	}

	@Override
	/**
	 * Returns a RealRational formed from given BigInteger numerator and
	 * denominator. Detects and protects against zero valued denominators. Moves
	 * any negation to the numerator. Simplifies the RealRational If numerator
	 * equals zero, simplifies to 0/1 regardless of denominator.
	 */
	public RealRational rational(BigInteger numerator, BigInteger denominator) {
		int signum = denominator.signum();
		RationalKey key;
		RealRational oldValue;

		if (signum == 0) {
			throw new ArithmeticException("Division by 0");
		}
		// ensures any negation is in numerator
		// protects signum method in RealRational
		if (signum < 0) {
			numerator = numerator.negate();
			denominator = denominator.negate();
		}
		// canonical form for 0 is 0/1 :
		if (numerator.signum() == 0) {
			denominator = BigInteger.ONE;
		} else if (!denominator.equals(BigInteger.ONE)) {
			BigInteger gcd = numerator.gcd(denominator);

			if (!gcd.equals(BigInteger.ONE)) {
				numerator = numerator.divide(gcd);
				denominator = denominator.divide(gcd);
			}
		}
		key = new RationalKey(numerator, denominator);
		oldValue = rationalMap.get(key);
		if (oldValue != null) {
			return oldValue;
		} else {
			RealRational newValue = new RealRational(numerator, denominator);

			rationalMap.put(key, newValue);
			return newValue;
		}
	}

	/**
	 * Returns true when a RealRational's denominator is equal to one.
	 * 
	 * @param arg0
	 * @return
	 */
	public boolean isIntegral(RealRational arg0) {
		return arg0.denominator().equals(BigInteger.ONE);
	}

	@Override
	/**
	 * An efficient way of adding two RationalNumbers.
	 */
	public RationalNumber add(RationalNumber arg0, RationalNumber arg1) {
		RealRational x = (RealRational) arg0;
		RealRational y = (RealRational) arg1;

		return rational(
				x.numerator().multiply(y.denominator())
						.add(x.denominator().multiply(y.numerator())), x
						.denominator().multiply(y.denominator()));
	}

	@Override
	/**
	 * An override of the add function to add two integers with precision
	 */
	public IntegerNumber add(IntegerNumber arg0, IntegerNumber arg1) {
		RealInteger x = (RealInteger) arg0;
		RealInteger y = (RealInteger) arg1;

		return integer(x.value().add(y.value()));
	}

	@Override
	/**
	 * returns an Integer of the quotient of numerator and denominator
	 */
	public IntegerNumber ceil(RationalNumber arg0) {
		RealRational x = (RealRational) arg0;
		BigInteger numerator = x.numerator();
		BigInteger denominator = x.denominator();
		BigInteger quotient = numerator.divide(denominator);

		if (numerator.signum() <= 0) {
			return integer(quotient);
		} else {
			BigInteger modulus = numerator.mod(denominator);

			if (modulus.equals(BigInteger.ZERO)) {
				return integer(quotient);
			} else {
				return integer(quotient.add(BigInteger.ONE));
			}
		}
	}

	@Override
	/**
	 * Determines the larger of two rationals returns 1 when the first argument
	 * is greater returns 0 when the rationals are equal returns -1 when the
	 * second argument is greater
	 */
	public int compare(RationalNumber arg0, RationalNumber arg1) {
		return arg0.numericalCompareTo(arg1);
	}

	@Override
	/**
	 * Determines the larger of two integers returns 1 when first argument is
	 * greater returns 0 when arguments are equal returns -1 when second
	 * argument is greater
	 */
	public int compare(IntegerNumber arg0, IntegerNumber arg1) {
		return arg0.numericalCompareTo(arg1);
	}

	@Override
	/**
	 * Takes two numbers as arguments and determines how to compare them based
	 * on their more specific identities.
	 */
	public int compare(Number arg0, Number arg1) {
		if (arg0 instanceof IntegerNumber && arg1 instanceof IntegerNumber) {
			return compare((IntegerNumber) arg0, (IntegerNumber) arg1);
		} else if (arg0 instanceof RationalNumber
				&& arg1 instanceof RationalNumber) {
			return compare((RationalNumber) arg0, (RationalNumber) arg1);
		} else {
			return compare(rational(arg0), rational(arg1));
		}
	}

	@Override
	/**
	 * Returns the integer form of the denominator of a rational
	 */
	public IntegerNumber denominator(RationalNumber arg0) {
		return integer(((RealRational) arg0).denominator());
	}

	@Override
	/**
	 * An override of the divide method to accommodate rationals
	 */
	public RationalNumber divide(RationalNumber arg0, RationalNumber arg1) {
		RealRational x = (RealRational) arg0;
		RealRational y = (RealRational) arg1;

		return rational(x.numerator().multiply(y.denominator()), x
				.denominator().multiply(y.numerator()));
	}

	@Override
	/**
	 * An override of the divide method to maintain precision
	 */
	public IntegerNumber divide(IntegerNumber arg0, IntegerNumber arg1) {
		RealInteger x = (RealInteger) arg0;
		RealInteger y = (RealInteger) arg1;

		return integer(x.value().divide(y.value()));
	}

	@Override
	/**
	 * Modulates argument one by argument two and returns the modulated integer
	 */
	public IntegerNumber mod(IntegerNumber arg0, IntegerNumber arg1) {
		RealInteger x = (RealInteger) arg0;
		RealInteger y = (RealInteger) arg1;

		if (y.signum() == 0)
			throw new IllegalArgumentException("Modulus divisor is zero");
		if (y.signum() < 0)
			if (x.signum() < 0)
				return negate(integer(x.value().abs().mod(y.value().abs())));
			else
				return integer(x.value().mod(y.value().abs()));
		else if (x.signum() < 0)
			return negate(integer(x.value().abs().mod(y.value())));
		return integer(x.value().mod(y.value()));
	}

	@Override
	/**
	 * Calculates the mathematical floor of a rational number
	 */
	public IntegerNumber floor(RationalNumber arg0) {
		RealRational x = (RealRational) arg0;
		BigInteger numerator = x.numerator();
		BigInteger denominator = x.denominator();
		BigInteger quotient = numerator.divide(denominator);

		if (numerator.signum() >= 0) {
			return integer(quotient);
		} else {
			BigInteger modulus = numerator.mod(denominator);

			if (modulus.equals(BigInteger.ZERO)) {
				return integer(quotient);
			} else {
				return integer(quotient.subtract(BigInteger.ONE));
			}
		}
	}

	@Override
	/**
	 * Creates and returns rationals from two integers
	 */
	public RealRational fraction(IntegerNumber numerator,
			IntegerNumber denominator) {
		RealInteger x = (RealInteger) numerator;
		RealInteger y = (RealInteger) denominator;

		return rational(x.value(), y.value());
	}

	@Override
	/**
	 * creates and returns integers from strings
	 */
	public IntegerNumber integer(String string) {
		return integer(new BigInteger(string));
	}

	@Override
	/**
	 * creates and returns rationals from integers by giving them one as a
	 * denominator
	 */
	public RationalNumber integerToRational(IntegerNumber integer) {
		RealInteger x = (RealInteger) integer;

		return rational(x.value(), BigInteger.ONE);
	}

	@Override
	/**
	 * Returns an integer from rationals that are integral
	 */
	public IntegerNumber integerValue(RationalNumber arg0) {
		RealRational x = (RealRational) arg0;

		if (!isIntegral(arg0)) {
			throw new ArithmeticException("Non-integral number: " + arg0);
		}
		return integer(x.numerator());
	}

	@Override
	/**
	 * Overrides the multiply class to deal with rationals
	 */
	public RationalNumber multiply(RationalNumber arg0, RationalNumber arg1) {
		RealRational x = (RealRational) arg0;
		RealRational y = (RealRational) arg1;

		return rational(x.numerator().multiply(y.numerator()), x.denominator()
				.multiply(y.denominator()));
	}

	@Override
	/**
	 * Overrides the multiply class to maintain precision
	 */
	public IntegerNumber multiply(IntegerNumber arg0, IntegerNumber arg1) {
		RealInteger x = (RealInteger) arg0;
		RealInteger y = (RealInteger) arg1;

		return integer(x.value().multiply(y.value()));
	}

	@Override
	/**
	 * negates the numerator of a rational number
	 */
	public RationalNumber negate(RationalNumber arg0) {
		RealRational x = (RealRational) arg0;

		return rational(x.numerator().negate(), x.denominator());
	}

	@Override
	/**
	 * negates an integer
	 */
	public IntegerNumber negate(IntegerNumber arg0) {
		RealInteger x = (RealInteger) arg0;

		return integer(x.value().negate());
	}

	@Override
	/**
	 * Determines how to represent a given string based on decimal point
	 * position returns an integer if a decimal point is not found returns a
	 * rational if a decimal point is found
	 */
	public Number number(String string) {
		int decimalPosition = string.indexOf('.');

		if (decimalPosition < 0) {
			return integer(string);
		} else {
			return rational(string);
		}
	}

	@Override
	/**
	 * Returns an integer from a rational number
	 */
	public IntegerNumber numerator(RationalNumber arg0) {
		return integer(((RealRational) arg0).numerator());
	}

	@Override
	/**
	 * returns an integer representation of one
	 */
	public IntegerNumber oneInteger() {
		return oneInteger;
	}

	@Override
	/**
	 * returns a rational representation of one
	 */
	public RationalNumber oneRational() {
		return oneRational;
	}

	@Override
	/**
	 * Returns a rationalNumber crafted from two string arguments
	 */
	public RationalNumber rational(String string) {
		int ePosition = string.indexOf('e');

		if (ePosition < 0) {
			return rationalWithoutE(string);
		} else {
			String left = string.substring(0, ePosition);
			RationalNumber result = rationalWithoutE(left);
			int length = string.length();
			boolean positive;
			String right;
			IntegerNumber exponent, power;
			RationalNumber powerReal;

			if (exponentiator == null)
				exponentiator = new Exponentiator<IntegerNumber>(multiplier,
						oneInteger);
			if (ePosition + 1 < length && string.charAt(ePosition + 1) == '+') {
				right = string.substring(ePosition + 2);
				positive = true;
			} else if (ePosition + 1 < length
					&& string.charAt(ePosition + 1) == '-') {
				right = string.substring(ePosition + 2);
				positive = false;
			} else {
				right = string.substring(ePosition + 1);
				positive = true;
			}
			exponent = integer(right);
			power = exponentiator.exp(tenInteger, exponent);
			powerReal = rational(power);
			if (!positive)
				result = divide(result, powerReal);
			else
				result = multiply(result, powerReal);
			return result;
		}

	}

	/**
	 * Returns a RationalNumber generated from two strings while simultaneously
	 * eliminating the value E from the strings
	 */
	public RationalNumber rationalWithoutE(String string) {
		String left, right; // substrings to left/right of decimal point
		int decimalPosition = string.indexOf('.');
		int rightLength;
		String powerOfTen = "1";

		if (decimalPosition < 0) { // no decimal
			left = string;
			right = "";
		} else if (decimalPosition == 0) {
			left = "";
			right = string.substring(1, string.length());
		} else {
			left = string.substring(0, decimalPosition);
			right = string.substring(decimalPosition + 1, string.length());
		}
		rightLength = right.length();
		for (int j = 0; j < rightLength; j++)
			powerOfTen += "0";
		return rational(new BigInteger(left + right),
				new BigInteger(powerOfTen));
	}

	@Override
	/**
	 * Determines how to represent two numbers as a RationalNumber based on
	 * their more specific classes
	 */
	public RationalNumber rational(Number number) {
		if (number instanceof RationalNumber) {
			return (RationalNumber) number;
		} else if (number instanceof IntegerNumber) {
			return integerToRational((IntegerNumber) number);
		}
		throw new IllegalArgumentException("Unknown type of number: " + number);
	}

	@Override
	/**
	 * An override of the subtract method to deal with RationalNumbers
	 */
	public RationalNumber subtract(RationalNumber arg0, RationalNumber arg1) {
		return add(arg0, negate(arg1));
	}

	@Override
	/**
	 * An override of the subtract method to maintain precision
	 */
	public IntegerNumber subtract(IntegerNumber arg0, IntegerNumber arg1) {
		RealInteger x = (RealInteger) arg0;
		RealInteger y = (RealInteger) arg1;

		return integer(x.value().subtract(y.value()));
	}

	@Override
	/**
	 * Returns an integer representation of zero
	 */
	public IntegerNumber zeroInteger() {
		return zeroInteger;
	}

	@Override
	/**
	 * Returns a rational representation of zero
	 */
	public RationalNumber zeroRational() {
		return zeroRational;
	}

	@Override
	/**
	 * Determines if a rational is integral by seeing if its denominator equates
	 * to one
	 */
	public boolean isIntegral(RationalNumber arg0) {
		RealRational x = (RealRational) arg0;

		return x.denominator().equals(BigInteger.ONE);
	}

	@Override
	/**
	 * Returns an integer representation of a value
	 */
	public IntegerNumber integer(int value) {
		return integer("" + value);
	}

	@Override
	/**
	 * Determines how to properly negate a number based on its more specific
	 * class
	 */
	public Number negate(Number arg0) {
		if (arg0 instanceof IntegerNumber)
			return negate((IntegerNumber) arg0);
		else
			return negate((RationalNumber) arg0);
	}

	@Override
	/**
	 * Determines how to properly add two numbers based on their more specific
	 * classes
	 */
	public Number add(Number arg0, Number arg1) {
		if (arg0 instanceof IntegerNumber) {
			if (!(arg1 instanceof IntegerNumber))
				throw new IllegalArgumentException(
						"Mixed numeric types not allowed:\n" + arg0 + "\n"
								+ arg1);
			return add((IntegerNumber) arg0, (IntegerNumber) arg1);
		} else if (arg0 instanceof RationalNumber) {
			if (!(arg1 instanceof RationalNumber))
				throw new IllegalArgumentException(
						"Mixed numeric types not allowed:\n" + arg0 + "\n"
								+ arg1);
			return add((RationalNumber) arg0, (RationalNumber) arg1);
		} else {
			throw new IllegalArgumentException("Unknown type of number: "
					+ arg0);
		}
	}

	@Override
	/**
	 * Determines how to properly divide two numbers based on their more
	 * specific classes
	 */
	public Number divide(Number arg0, Number arg1) {
		if (arg0 instanceof IntegerNumber) {
			if (!(arg1 instanceof IntegerNumber))
				throw new IllegalArgumentException(
						"Mixed numeric types not allowed:\n" + arg0 + "\n"
								+ arg1);
			return divide((IntegerNumber) arg0, (IntegerNumber) arg1);
		} else if (arg0 instanceof RationalNumber) {
			if (!(arg1 instanceof RationalNumber))
				throw new IllegalArgumentException(
						"Mixed numeric types not allowed:\n" + arg0 + "\n"
								+ arg1);
			return divide((RationalNumber) arg0, (RationalNumber) arg1);
		} else {
			throw new IllegalArgumentException("Unknown type of number: "
					+ arg0);
		}
	}

	@Override
	/**
	 * Determines how to properly multiply two numbers based on their more
	 * specific classes
	 */
	public Number multiply(Number arg0, Number arg1) {
		if (arg0 instanceof IntegerNumber) {
			if (!(arg1 instanceof IntegerNumber))
				throw new IllegalArgumentException(
						"Mixed numeric types not allowed:\n" + arg0 + "\n"
								+ arg1);
			return multiply((IntegerNumber) arg0, (IntegerNumber) arg1);
		} else if (arg0 instanceof RationalNumber) {
			if (!(arg1 instanceof RationalNumber))
				throw new IllegalArgumentException(
						"Mixed numeric types not allowed:\n" + arg0 + "\n"
								+ arg1);
			return multiply((RationalNumber) arg0, (RationalNumber) arg1);
		} else {
			throw new IllegalArgumentException("Unknown type of number: "
					+ arg0);
		}
	}

	@Override
	/**
	 * Determines how to properly subtract two numbers based on their more
	 * specific classes
	 */
	public Number subtract(Number arg0, Number arg1) {
		if (arg0 instanceof IntegerNumber) {
			if (!(arg1 instanceof IntegerNumber))
				throw new IllegalArgumentException(
						"Mixed numeric types not allowed:\n" + arg0 + "\n"
								+ arg1);
			return subtract((IntegerNumber) arg0, (IntegerNumber) arg1);
		} else if (arg0 instanceof RationalNumber) {
			if (!(arg1 instanceof RationalNumber))
				throw new IllegalArgumentException(
						"Mixed numeric types not allowed:\n" + arg0 + "\n"
								+ arg1);
			return subtract((RationalNumber) arg0, (RationalNumber) arg1);
		} else {
			throw new IllegalArgumentException("Unknown type of number: "
					+ arg0);
		}
	}

	@Override
	/**
	 * Returns a RationalNumber incremented by one
	 */
	public RationalNumber increment(RationalNumber arg) {
		return add(arg, oneRational);
	}

	@Override
	/**
	 * Returns an IntegerNumber incremented by one
	 */
	public IntegerNumber increment(IntegerNumber arg) {
		return add(arg, oneInteger);
	}

	@Override
	/**
	 * Determines how to properly increment a number based on its more specific
	 * class
	 */
	public Number increment(Number arg) {
		if (arg instanceof IntegerNumber)
			return add((IntegerNumber) arg, oneInteger);
		return add((RationalNumber) arg, oneRational);
	}

	@Override
	/**
	 * Returns a RationalNumber decremented by one
	 */
	public RationalNumber decrement(RationalNumber arg) {
		return subtract(arg, oneRational);
	}

	@Override
	/**
	 * Returns an IntegerNumber decremented by one
	 */
	public IntegerNumber decrement(IntegerNumber arg) {
		return subtract(arg, oneInteger);
	}

	@Override
	/**
	 * Determines how to properly decrement a number based on its more specific
	 * class
	 */
	public Number decrement(Number arg) {
		if (arg instanceof IntegerNumber)
			return subtract((IntegerNumber) arg, oneInteger);
		return subtract((RationalNumber) arg, oneRational);
	}

	@Override
	/**
	 * Sends BigInteger representations of given IntegerNumbers to the gcd
	 * function
	 */
	public IntegerNumber gcd(IntegerNumber arg0, IntegerNumber arg1) {
		BigInteger value0 = ((RealInteger) arg0).value();
		BigInteger value1 = ((RealInteger) arg1).value();

		return integer(value0.gcd(value1));
	}

	@Override
	/**
	 * Determines and returns the lcm of two IntegerNumbers by dividing their
	 * product by their gcd
	 */
	public IntegerNumber lcm(IntegerNumber arg0, IntegerNumber arg1) {
		return divide(multiply(arg0, arg1), gcd(arg0, arg1));
	}

	/**
	 * A simple method to print a matrix of RationalNumbers to screen
	 * 
	 * @param out
	 * @param msg
	 * @param matrix
	 */
	public void printMatrix(PrintWriter out, String msg,
			RationalNumber[][] matrix) {
		out.println(msg);
		for (int i = 0; i < matrix.length; i++) {
			RationalNumber[] row = matrix[i];

			for (int j = 0; j < row.length; j++) {
				out.print(row[j] + "  ");
			}
			out.println();
		}
		out.println();
		out.flush();
	}

	@Override
	/**
	 * Performs a gaussian elimination on the given RationalNumber matrix
	 * Maintains a boolean 'debug' for easy troubleshooting due to its complex
	 * nature
	 */
	public void gaussianElimination(RationalNumber[][] matrix) {
		int numRows = matrix.length;
		int numCols;
		int top = 0; // index of current top row
		int col = 0; // index of current left column
		int pivotRow = 0; // index of row containing the pivot
		RationalNumber pivot = zeroRational; // the value of the pivot
		int i = 0; // loop variable over rows of matrix
		int j = 0; // loop variable over columns of matrix
		boolean debug = false;
		PrintWriter out = new PrintWriter(System.out);

		if (numRows == 0)
			return;
		numCols = matrix[0].length;

		for (top = col = 0; top < numRows && col < numCols; top++, col++) {
			/*
			 * At this point we know that the submatarix consisting of the first
			 * top rows of A is in reduced row-echelon form. We will now
			 * consider the submatrix B consisting of the remaining rows. We
			 * know, additionally, that the first col columns of B are all zero.
			 */

			if (debug)
				out.println("Top: " + top + "\n");

			/*
			 * Step 1: Locate the leftmost column of B that does not consist
			 * entirely of zeros, if one exists. The top nonzero entry of this
			 * column is the pivot.
			 */

			pivot = zeroRational;
			pivotSearch: for (; col < numCols; col++) {
				for (pivotRow = top; pivotRow < numRows; pivotRow++) {
					pivot = matrix[pivotRow][col];
					if (!pivot.isZero())
						break pivotSearch;
				}
			}

			if (col >= numCols) {
				break;
			}

			/*
			 * At this point we are guaranteed that pivot = A[pivotRow,col] is
			 * nonzero. We also know that all the columns of B to the left of
			 * col consist entirely of zeros.
			 */

			if (debug) {
				out.println("Step 1 result: col=" + col + ", pivotRow="
						+ pivotRow + ", pivot=" + pivot + "\n");
			}

			/*
			 * Step 2: Interchange the top row with the pivot row, if necessary,
			 * so that the entry at the top of the column found in Step 1 is
			 * nonzero.
			 */

			if (pivotRow != top) {
				RationalNumber[] tmpRow = matrix[top];

				matrix[top] = matrix[pivotRow];
				matrix[pivotRow] = tmpRow;
			}

			if (debug) {
				printMatrix(out, "Step 2 result:\n", matrix);
			}

			/*
			 * At this point we are guaranteed that A[top,col] = pivot is
			 * nonzero. Also, we know that (i>=top and j<col) implies A[i,j] =
			 * 0.
			 */

			/*
			 * Step 3: Divide the top row by pivot in order to introduce a
			 * leading 1.
			 */

			if (!pivot.isOne())
				for (j = col; j < numCols; j++) {
					matrix[top][j] = divide(matrix[top][j], pivot);
				}

			if (debug) {
				printMatrix(out, "Step 3 result:\n", matrix);
			}

			/*
			 * At this point we are guaranteed that A[top,col] is 1.0, assuming
			 * that floating point arithmetic guarantees that a/a equals 1.0 for
			 * any nonzero double a.
			 */

			/*
			 * Step 4: Add suitable multiples of the top row to all other rows
			 * so that all entries above and below the leading 1 become zero.
			 */

			for (i = 0; i < numRows; i++) {
				if (i != top) {
					RationalNumber tmp = matrix[i][col];
					for (j = col; j < numCols; j++) {
						matrix[i][j] = subtract(matrix[i][j],
								multiply(tmp, matrix[top][j]));
					}
				}
			}

			if (debug) {
				printMatrix(out, "Step 4 result:\n", matrix);
			}
		}
	}

	@Override
	public Interval emptyIntegerInterval() {
		return emptyIntegerInterval;
	}

	@Override
	public Interval emptyRealInterval() {
		return emptyRationalInterval;
	}

	@Override
	public Interval newInterval(boolean isIntegral, Number lower,
			boolean strictLower, Number upper, boolean strictUpper) {
		assert lower == null || (isIntegral == lower instanceof IntegerNumber);
		assert upper == null || (isIntegral == upper instanceof IntegerNumber);
		if (isIntegral) {
			// Adjust the strict and bound for integral intervals
			if (lower != null && strictLower) {
				lower = add(lower, oneInteger);
				strictLower = false;
			}
			if (upper != null && strictUpper) {
				upper = subtract(upper, oneInteger);
				strictUpper = false;
			}
		}
		if (lower != null && upper != null) {
			// Check the illegal interval arguments.
			int compareUpperLower = upper.numericalCompareTo(lower);

			if ((compareUpperLower < 0)
					|| (compareUpperLower == 0 && (strictLower || strictUpper))) {
				return isIntegral ? emptyIntegerInterval
						: emptyRationalInterval;
			}
		}
		return new CommonInterval(isIntegral, lower, strictLower, upper,
				strictUpper);
	}

	@Override
	public Interval intersection(Interval i1, Interval i2) {
		assert i1 != null && i2 != null;

		boolean isIntegral = i1.isIntegral();

		assert isIntegral == i2.isIntegral();

		Number lo1 = i1.lower();
		Number lo2 = i2.lower();
		Number up1 = i1.upper();
		Number up2 = i2.upper();
		Number lo, up;
		boolean sl1 = i1.strictLower();
		boolean sl2 = i2.strictLower();
		boolean su1 = i1.strictUpper();
		boolean su2 = i2.strictUpper();
		boolean sl, su;

		if (lo1 == NEG_INFINITY) {
			lo = lo2;
			sl = sl2;
		} else if (lo2 == NEG_INFINITY) {
			lo = lo1;
			sl = sl1;
		} else {
			int compare = lo1.numericalCompareTo(lo2);

			if (compare < 0) {
				lo = lo2;
				sl = sl2;
			} else if (compare == 0) {
				lo = lo1;
				sl = sl1 || sl2;
			} else {
				lo = lo1;
				sl = sl1;
			}
		}
		if (up1 == POS_INFINITY) {
			up = up2;
			su = su2;
		} else if (up2 == POS_INFINITY) {
			up = up1;
			su = su1;
		} else {
			int compare = up1.numericalCompareTo(up2);

			if (compare > 0) {
				up = up2;
				su = su2;
			} else if (compare == 0) {
				up = up1;
				su = su1 || su2;
			} else {
				up = up1;
				su = su1;
			}
		}
		if (lo != NEG_INFINITY && up != POS_INFINITY) {
			int compare = up.numericalCompareTo(lo);

			if (compare < 0) {
				return isIntegral ? emptyIntegerInterval
						: emptyRationalInterval;
			} else if (compare == 0) {
				if (sl || su) {
					return isIntegral ? emptyIntegerInterval
							: emptyRationalInterval;
				}
			}
		}
		return new CommonInterval(isIntegral, lo, sl, up, su);
	}

	@Override
	public void union(Interval i1, Interval i2, IntervalUnion result) {
		assert i1 != null && i2 != null && result != null;

		boolean isIntegral = i1.isIntegral();

		assert i1.isIntegral() == i2.isIntegral();

		if (i1.isEmpty() || i2.isUniversal()) {
			// Exactly a single interval
			result.status = 0;
			result.union = i2;
			return;
		} else if (i2.isEmpty() || i1.isUniversal()) {
			// Exactly a single interval
			result.status = 0;
			result.union = i1;
			return;
		} else {
			Number lo2 = i2.lower();
			Number up1 = i1.upper();
			boolean sl2 = i2.strictLower();
			boolean su1 = i1.strictUpper();
			boolean su2 = i2.strictUpper();
			int compareUp1Lo2 = (up1 == POS_INFINITY || lo2 == NEG_INFINITY) ? 1
					: up1.numericalCompareTo(lo2);

			if (compareUp1Lo2 > 0) {
				Number lo1 = i1.lower();
				Number up2 = i2.upper();
				boolean sl1 = i1.strictLower();
				int compareLo1Up2 = (lo1 == NEG_INFINITY || up2 == POS_INFINITY) ? -1
						: lo1.numericalCompareTo(up2);

				if (compareLo1Up2 < 0) {
					// Intersected
					Number lo = NEG_INFINITY, up = POS_INFINITY;
					boolean sl = false, su = false;
					int compareLo1Lo2 = lo1 == NEG_INFINITY ? -1
							: lo2 == NEG_INFINITY ? 1 : lo1
									.numericalCompareTo(lo2);
					int compareUp1Up2 = up1 == POS_INFINITY ? 1
							: up2 == POS_INFINITY ? -1 : up1
									.numericalCompareTo(up2);

					if (compareLo1Lo2 < 0) { // lo1<lo2
						lo = lo1;
						sl = sl1;
					} else if (compareLo1Lo2 == 0) {
						lo = lo1;
						sl = sl1 && sl2;
					} else {
						lo = lo2;
						sl = sl2;
					}
					if (compareUp1Up2 < 0) {
						up = up2;
						su = su2;
					} else if (compareUp1Up2 == 0) {
						up = up1;
						su = su1 && su2;
					} else {
						up = up1;
						su = su1;
					}
					result.status = 0;
					result.union = new CommonInterval(isIntegral, lo, sl, up,
							su);
					return;
				} else if (compareLo1Up2 == 0 && (!sl1 || !su2)) {
					// Connected
					result.status = 0;
					result.union = new CommonInterval(isIntegral, lo2, sl2,
							up1, su1);
					return;
				} else {
					// Disjoint
					result.status = 1;
					result.union = null;
					return;
				}
			} else if (compareUp1Lo2 == 0 && (!su1 || !su2)) {
				// Connected
				Number lo1 = i1.lower();
				Number up2 = i2.upper();
				boolean sl1 = i1.strictLower();

				result.status = 0;
				result.union = new CommonInterval(isIntegral, lo1, sl1, up2,
						su2);
				return;
			} else {
				// Disjoint
				result.status = -1;
				result.union = null;
				return;
			}
		}
	}

	@Override
	public Interval affineTransform(Interval itv, Number a, Number b) {
		assert itv != null && a != null && b != null;

		boolean isIntegral = itv.isIntegral();

		assert isIntegral == a instanceof IntegerNumber;
		assert isIntegral == b instanceof IntegerNumber;

		if (itv.isEmpty())
			return isIntegral ? emptyIntegerInterval : emptyRationalInterval;

		Number lo = itv.lower();
		Number up = itv.upper();
		boolean sl = itv.strictLower();
		boolean su = itv.strictUpper();

		// New upper and lower of result.union.
		lo = lo == null ? null : add(multiply(lo, a), b);
		up = up == null ? null : add(multiply(up, a), b);
		if (a.signum() < 0)
			return new CommonInterval(isIntegral, up, su, lo, sl);
		else if (a.signum() == 0)
			return new CommonInterval(isIntegral, b, false, b, false);
		else
			return new CommonInterval(isIntegral, lo, sl, up, su);
	}

	@Override
	public int compare(Interval i1, Interval i2) {
		assert i1 != null && i2 != null;

		boolean isIntegral = i1.isIntegral();

		assert isIntegral == i2.isIntegral();

		// int contains1 = 1; // i2 contains i1
		int cmpL1L2 = 0, cmpL1U2 = 0;
		int cmpU1L2 = 0, cmpU1U2 = 0;
		Number lo1 = i1.lower(), lo2 = i2.lower();
		Number up1 = i1.upper(), up2 = i2.upper();
		boolean sl1 = i1.strictLower(), sl2 = i2.strictLower();
		boolean su1 = i1.strictUpper(), su2 = i2.strictUpper();

		if (i1.isEmpty() && i2.isEmpty()) {
			return EXACTLY_SAME;
		} else if (i1.isEmpty()) {
			return CONTAINED_IN_INTERVAL2;
		} else if (i2.isEmpty()) {
			return CONTAINED_IN_INTERVAL1;
		}

		if (lo1 == null && lo2 == null) {
			cmpL1L2 = 0;
		} else if (lo1 == null) {
			cmpL1L2 = -1;
		} else if (lo2 == null) {
			cmpL1L2 = 1;
		} else {
			cmpL1L2 = compare(lo1, lo2);
		}
		if (up1 == null && up2 == null) {
			cmpU1U2 = 0;
		} else if (up1 == null) {
			cmpU1U2 = 1;
		} else if (up2 == null) {
			cmpU1U2 = -1;
		} else {
			cmpU1U2 = compare(up1, up2);
		}
		if (cmpL1L2 < 0) {
			if (cmpU1U2 < 0) {
				cmpU1L2 = compare(up1, lo2);
				if (cmpU1L2 < 0) {
					return LEFT_DISJOINTED;
				} else if (cmpU1L2 > 0) {
					return LEFT_INTERSECTED;
				} else {
					if (!su1 && !sl2) {
						return LEFT_INTERSECTED;
					} else {
						return LEFT_DISJOINTED;
					}
				}
			} else if (cmpU1U2 > 0) {
				return CONTAINED_IN_INTERVAL1;
			} else {
				if (up1 == null || lo2 == null) {
					cmpU1L2 = 1;
				} else {
					cmpU1L2 = compare(up1, lo2);
				}
				if (su1 && cmpU1L2 == 0) {
					return LEFT_DISJOINTED;
				} else if (su1 && !su2 && cmpU1L2 > 0) {
					return LEFT_INTERSECTED;
				} else {
					return CONTAINED_IN_INTERVAL1;
				}
			}
		} else if (cmpL1L2 > 0) {
			if (cmpU1U2 < 0) {
				return CONTAINED_IN_INTERVAL2;
			} else if (cmpU1U2 > 0) {
				cmpL1U2 = compare(lo1, up2);
				if (cmpL1U2 < 0) {
					return RIGHT_INTERSECTED;
				} else if (cmpL1U2 > 0) {
					return RIGHT_DISJOINTED;
				} else {
					if (!sl1 && !su2) {
						return RIGHT_INTERSECTED;
					} else {
						return RIGHT_DISJOINTED;
					}
				}
			} else {
				if (lo1 == null || up2 == null) {
					cmpL1U2 = -1;
				} else {
					cmpL1U2 = compare(lo1, up2);
				}
				if (su2 && cmpL1U2 == 0) {
					return RIGHT_DISJOINTED;
				} else if (!su1 && su2 && cmpL1U2 < 0) {
					return RIGHT_INTERSECTED;
				} else {
					return CONTAINED_IN_INTERVAL2;
				}
			}
		} else {
			if (cmpU1U2 < 0) {
				if (up1 == null || lo2 == null) {
					cmpU1L2 = 1;
				} else {
					cmpU1L2 = compare(up1, lo2);
				}
				if (cmpU1L2 == 0) {
					if (sl2) {
						return LEFT_DISJOINTED;
					} else {
						return CONTAINED_IN_INTERVAL2;
					}
				} else if (cmpU1L2 > 0) {
					if (!sl1 && sl2) {
						return LEFT_INTERSECTED;
					} else {
						return CONTAINED_IN_INTERVAL2;
					}
				}
			} else if (cmpU1U2 > 0) {
				if (lo1 == null || up2 == null) {
					cmpL1U2 = -1;
				} else {
					cmpL1U2 = compare(lo1, up2);
				}
				if (cmpL1U2 == 0) {
					if (sl1) {
						return RIGHT_DISJOINTED;
					} else {
						return CONTAINED_IN_INTERVAL1;
					}
				} else if (cmpL1U2 < 0) {
					if (sl1 && !sl2) {
						return RIGHT_INTERSECTED;
					} else {
						return CONTAINED_IN_INTERVAL1;
					}
				}
			} else {
				if (sl1 && !sl2) {
					if (!su1 && su2) {
						return RIGHT_INTERSECTED;
					} else {
						return CONTAINED_IN_INTERVAL2;
					}
				} else if (!sl1 && sl2) {
					if (su1 && !su2) {
						return LEFT_INTERSECTED;
					} else {
						return CONTAINED_IN_INTERVAL1;
					}
				} else {
					if (su1 && !su2) {
						return CONTAINED_IN_INTERVAL2;
					} else if (!su1 && su2) {
						return CONTAINED_IN_INTERVAL1;
					} // else Exactly Same
				}
			}
		}
		return EXACTLY_SAME;
	}

	@Override
	public Interval add(Interval i1, Interval i2) {
		assert !i1.isEmpty() && !i2.isEmpty();
		assert i1.isIntegral() == i2.isIntegral();

		Number lo1 = i1.lower();
		Number up1 = i1.upper();
		Number lo2 = i2.lower();
		Number up2 = i2.upper();
		boolean sl1 = i1.strictLower();
		boolean su1 = i1.strictUpper();
		boolean sl2 = i2.strictLower();
		boolean su2 = i2.strictUpper();
		boolean isIntegral = i1.isIntegral();

		if (i1.isUniversal() || i2.isUniversal()) {
			return newInterval(isIntegral, null, true, null, true);
		} else {
			Number lo = null;
			Number up = null;
			boolean sl = true;
			boolean su = true;

			if (lo1 != null && lo2 != null) {
				if (!sl1 && !sl2) {
					sl = false;
				}
				lo = add(lo1, lo2);
			}
			if (up1 != null && up2 != null) {
				if (!su1 && !su2) {
					su = false;
				}
				up = add(up1, up2);
			}
			return newInterval(isIntegral, lo, sl, up, su);
		}
	}

	@Override
	public Interval multiply(Interval i1, Interval i2) {
		assert !i1.isEmpty() && !i2.isEmpty();
		assert i1.isIntegral() == i2.isIntegral();

		Number lo1 = i1.lower();
		Number up1 = i1.upper();
		Number lo2 = i2.lower();
		Number up2 = i2.upper();
		Number lo = null;
		Number up = null;
		boolean sl1 = i1.strictLower();
		boolean su1 = i1.strictUpper();
		boolean sl2 = i2.strictLower();
		boolean su2 = i2.strictUpper();
		boolean sl = true;
		boolean su = true;
		boolean isIntegral = i1.isIntegral();

		if (i1.isZero() || i2.isZero()) {
			Number zeroNum = isIntegral ? zeroInteger : zeroRational;

			return newInterval(isIntegral, zeroNum, false, zeroNum, false);
		} else if (i1.isUniversal() || i2.isUniversal()) {
			return newInterval(isIntegral, lo, sl, up, su);
		} else if (lo1 == null && lo2 == null) {
			int signumUp1 = su1 ? up1.signum() * 2 - 1 : up1.signum();
			int signumUp2 = su2 ? up2.signum() * 2 - 1 : up2.signum();

			if (signumUp1 > 0 || signumUp2 > 0) {
				return newInterval(isIntegral, lo, sl, up, su);
			} else {
				sl = (su1 || su2) && (su1 || !up1.isZero())
						&& (su2 || !up2.isZero());
				lo = multiply(up1, up2);
				return newInterval(isIntegral, lo, sl, up, su);
			}
		} else if (lo1 == null && up2 == null) {
			int signumUp1 = su1 ? up1.signum() * 2 - 1 : up1.signum();
			int signumLo2 = sl2 ? lo2.signum() * 2 + 1 : lo2.signum();

			if (signumUp1 > 0 || signumLo2 < 0) {
				return newInterval(isIntegral, lo, sl, up, su);
			} else {
				su = (su1 || sl2) && (su1 || !up1.isZero())
						&& (sl2 || !lo2.isZero());
				up = multiply(up1, lo2);
				return newInterval(isIntegral, lo, sl, up, su);
			}
		} else if (up1 == null && lo2 == null) {
			int signumLo1 = sl1 ? lo1.signum() * 2 + 1 : lo1.signum();
			int signumUp2 = su2 ? up2.signum() * 2 - 1 : up2.signum();

			if (signumLo1 < 0 || signumUp2 > 0) {
				return newInterval(isIntegral, lo, sl, up, su);
			} else {
				su = (sl1 || su2) && (sl1 || !lo1.isZero())
						&& (su2 || !up2.isZero());
				up = multiply(lo1, up2);
				return newInterval(isIntegral, lo, sl, up, su);
			}
		} else if (up1 == null && up2 == null) {
			int signumLo1 = sl1 ? lo1.signum() * 2 + 1 : lo1.signum();
			int signumLo2 = sl2 ? lo2.signum() * 2 + 1 : lo2.signum();

			if (signumLo1 < 0 || signumLo2 < 0) {
				return newInterval(isIntegral, lo, sl, up, su);
			} else {
				sl = (sl1 || sl2) && (sl1 || !lo1.isZero())
						&& (sl2 || !lo2.isZero());
				lo = multiply(lo1, lo2);
				return newInterval(isIntegral, lo, sl, up, su);
			}
		} else if (lo1 == null) {
			int signumLo2 = sl2 ? lo2.signum() * 2 + 1 : lo2.signum();
			int signumUp1 = su1 ? up1.signum() * 2 - 1 : up1.signum();
			int signumUp2 = su2 ? up2.signum() * 2 - 1 : up2.signum();

			if (signumLo2 >= 0) {
				if (signumUp1 <= 0) {
					su = (su1 || sl2) && (su1 || !up1.isZero())
							&& (sl2 || !lo2.isZero());
					up = multiply(up1, lo2);
					return newInterval(isIntegral, lo, sl, up, su);
				} else {
					su = (su1 || su2) && (su2 || !up2.isZero());
					up = multiply(up1, up2);
					return newInterval(isIntegral, lo, sl, up, su);
				}
			} else if (signumUp2 <= 0) {
				if (signumUp1 <= 0) {
					sl = (su1 || su2) && (su1 || !up1.isZero())
							&& (su2 || !up2.isZero());
					lo = multiply(up1, up2);
					return newInterval(isIntegral, lo, sl, up, su);
				} else {
					sl = su1 || sl2;
					lo = multiply(up1, lo2);
					return newInterval(isIntegral, lo, sl, up, su);
				}
			} else {
				return newInterval(isIntegral, lo, sl, up, su);
			}
		} else if (up1 == null) {
			int signumLo1 = sl1 ? lo1.signum() * 2 + 1 : lo1.signum();
			int signumLo2 = sl2 ? lo2.signum() * 2 + 1 : lo2.signum();
			int signumUp2 = su2 ? up2.signum() * 2 - 1 : up2.signum();

			if (signumLo2 >= 0) {
				if (signumLo1 >= 0) {
					sl = (sl1 || sl2) && (sl1 || !lo1.isZero())
							&& (sl2 || !lo2.isZero());
					lo = multiply(lo1, lo2);
					return newInterval(isIntegral, lo, sl, up, su);
				} else {
					sl = (sl1 || su2) && (su2 || !up2.isZero());
					lo = multiply(lo1, up2);
					return newInterval(isIntegral, lo, sl, up, su);
				}
			} else if (signumUp2 <= 0) {
				if (signumLo1 >= 0) {
					su = (sl1 || su2) && (sl1 || !lo1.isZero())
							&& (su2 || !up2.isZero());
					up = multiply(lo1, up2);
					return newInterval(isIntegral, lo, sl, up, su);
				} else {
					su = sl1 || sl2;
					up = multiply(lo1, lo2);
					return newInterval(isIntegral, lo, sl, up, su);
				}
			} else {
				return newInterval(isIntegral, lo, sl, up, su);
			}
		} else if (lo2 == null) {
			int signumLo1 = sl1 ? lo1.signum() * 2 + 1 : lo1.signum();
			int signumUp1 = su1 ? up1.signum() * 2 - 1 : up1.signum();
			int signumUp2 = su2 ? up2.signum() * 2 - 1 : up2.signum();

			if (signumLo1 >= 0) {
				if (signumUp2 <= 0) {
					su = (sl1 || su2) && (sl1 || !lo1.isZero())
							&& (su2 || !up2.isZero());
					up = multiply(lo1, up2);
					return newInterval(isIntegral, lo, sl, up, su);
				} else {
					su = (su1 || su2) && (su1 || !up1.isZero());
					up = multiply(up1, up2);
					return newInterval(isIntegral, lo, sl, up, su);
				}
			} else if (signumUp1 <= 0) {
				if (signumUp2 <= 0) {
					sl = (su1 || su2) && (su1 || !up1.isZero())
							&& (su2 || !up2.isZero());
					lo = multiply(up1, up2);
					return newInterval(isIntegral, lo, sl, up, su);
				} else {
					sl = sl1 || su2;
					lo = multiply(lo1, up2);
					return newInterval(isIntegral, lo, sl, up, su);
				}
			} else {
				return newInterval(isIntegral, lo, sl, up, su);
			}
		} else if (up2 == null) {
			int signumLo1 = sl1 ? lo1.signum() * 2 + 1 : lo1.signum();
			int signumLo2 = sl2 ? lo2.signum() * 2 + 1 : lo2.signum();
			int signumUp1 = su1 ? up1.signum() * 2 - 1 : up1.signum();

			if (signumLo1 >= 0) {
				if (signumLo2 >= 0) {
					sl = (sl1 || sl2) && (sl1 || !lo1.isZero())
							&& (sl2 || !lo2.isZero());
					lo = multiply(lo1, lo2);
					return newInterval(isIntegral, lo, sl, up, su);
				} else {
					sl = (su1 || sl2) && (su1 || !up1.isZero());
					lo = multiply(up1, lo2);
					return newInterval(isIntegral, lo, sl, up, su);
				}
			} else if (signumUp1 <= 0) {
				if (signumLo2 >= 0) {
					su = (su1 || sl2) && (su1 || !up1.isZero())
							&& (sl2 || !lo2.isZero());
					up = multiply(up1, lo2);
					return newInterval(isIntegral, lo, sl, up, su);
				} else {
					su = sl1 || sl2;
					up = multiply(lo1, lo2);
					return newInterval(isIntegral, lo, sl, up, su);
				}
			} else {
				return newInterval(isIntegral, lo, sl, up, su);
			}
		} else {
			int signumLo1 = sl1 ? lo1.signum() * 2 + 1 : lo1.signum();
			int signumLo2 = sl2 ? lo2.signum() * 2 + 1 : lo2.signum();
			int signumUp1 = su1 ? up1.signum() * 2 - 1 : up1.signum();
			int signumUp2 = su2 ? up2.signum() * 2 - 1 : up2.signum();

			if (signumLo1 >= 0) {
				if (signumLo2 >= 0) {
					lo = multiply(lo1, lo2);
					sl = (sl1 || sl2) && (sl1 || !lo1.isZero())
							&& (sl2 || !lo2.isZero());
					up = multiply(up1, up2);
					su = (su1 || su2) && (su1 || !up1.isZero())
							&& (su2 || !up2.isZero());
					return newInterval(isIntegral, lo, sl, up, su);
				} else if (signumUp2 <= 0) {
					lo = multiply(up1, lo2);
					sl = (su1 || sl2) && (su1 || !up1.isZero());
					up = multiply(lo1, up2);
					su = (sl1 || su2) && (sl1 || !lo1.isZero())
							&& (su2 || !up2.isZero());
					return newInterval(isIntegral, lo, sl, up, su);
				} else {
					lo = multiply(up1, lo2);
					sl = (su1 || sl2) && (su1 || !up1.isZero());
					up = multiply(up1, up2);
					su = (su1 || su2) && (su1 || !up1.isZero());
					return newInterval(isIntegral, lo, sl, up, su);
				}
			} else if (signumUp1 <= 0) {
				if (signumLo2 >= 0) {
					lo = multiply(lo1, up2);
					sl = (sl1 || su2) && (su2 || !up2.isZero());
					up = multiply(up1, lo2);
					su = (su1 || sl2) && (su1 || !up1.isZero())
							&& (sl2 || !lo2.isZero());
					return newInterval(isIntegral, lo, sl, up, su);
				} else if (signumUp2 <= 0) {
					lo = multiply(up1, up2);
					sl = (su1 || su2) && (su1 || !up1.isZero())
							&& (su2 || !up2.isZero());
					up = multiply(lo1, lo2);
					su = sl1 || sl2;
					return newInterval(isIntegral, lo, sl, up, su);
				} else {
					lo = multiply(lo1, up2);
					sl = sl1 || su2;
					up = multiply(lo1, lo2);
					su = sl1 || sl2;
					return newInterval(isIntegral, lo, sl, up, su);
				}
			} else {
				if (signumLo2 >= 0) {
					lo = multiply(lo1, up2);
					sl = (sl1 || su2) && (su2 || !up2.isZero());
					up = multiply(up1, up2);
					su = (su1 || su2) && (su2 || !up2.isZero());
					return newInterval(isIntegral, lo, sl, up, su);
				} else if (signumUp2 <= 0) {
					lo = multiply(up1, lo2);
					sl = su1 || sl2;
					up = multiply(lo1, lo2);
					su = sl1 || sl2;
					return newInterval(isIntegral, lo, sl, up, su);
				} else {
					Number lo1lo2 = multiply(lo1, lo2);
					Number up1up2 = multiply(up1, up2);
					Number lo1up2 = multiply(lo1, up2);
					Number up1lo2 = multiply(up1, lo2);

					if (lo1lo2.compareTo(up1up2) < 0) {
						up = up1up2;
						su = su1 || su2;
					} else if (lo1lo2.compareTo(up1up2) > 0) {
						up = lo1lo2;
						su = sl1 || sl2;
					} else {
						up = lo1lo2;
						su = (sl1 || sl2) && (su1 || su2);
					}
					if (lo1up2.compareTo(up1lo2) < 0) {
						lo = lo1up2;
						sl = sl1 || su2;
					} else if (lo1up2.compareTo(up1lo2) > 0) {
						lo = up1lo2;
						sl = su1 || sl2;
					} else {
						lo = up1lo2;
						sl = (sl1 || su2) && (su1 || sl2);
					}
					return newInterval(isIntegral, lo, sl, up, su);
				}
			}
		}
	}

	@Override
	public Interval power(Interval interval, int exp) {
		assert interval != null;
		assert !(interval.isZero() && exp == 0);

		boolean strictLower = interval.strictLower();
		boolean strictUpper = interval.strictUpper();
		boolean newSl = true;
		boolean newSu = true;
		boolean isIntegral = interval.isIntegral();
		Number lower = interval.lower();
		Number upper = interval.upper();
		Number newLo = null;
		Number newUp = null;
		Number oneNumber = isIntegral ? oneInteger : oneRational;
		Number zeroNumber = isIntegral ? zeroInteger : zeroRational;

		if (exp == 0) {
			return newInterval(isIntegral, oneNumber, false, oneNumber, false);
		} else if (exp > 0) {
			if (interval.isUniversal()) {
				return newInterval(isIntegral, lower, strictLower, upper,
						strictUpper);
			} else if (lower == null) {
				int signumUp = strictUpper ? upper.signum() * 2 - 1 : upper
						.signum();

				if (signumUp < 0) {
					if (exp % 2 == 0) {
						newLo = power(negate(upper), exp);
						newSl = strictUpper;
					} else {
						newUp = power(upper, exp);
						newSu = strictUpper;
					}
				} else {
					if (exp % 2 == 0) {
						newLo = zeroNumber;
						newSl = false;
					} else {
						newUp = power(upper, exp);
						newSu = strictUpper;
					}
				}
				return newInterval(isIntegral, newLo, newSl, newUp, newSu);
			} else if (upper == null) {
				int signumLo = strictLower ? lower.signum() * 2 + 1 : lower
						.signum();

				if (signumLo > 0) {
					newLo = power(lower, exp);
					newSl = strictLower;
				} else {
					if (exp % 2 == 0) {
						newLo = zeroNumber;
						newSl = false;
					} else {
						newLo = power(lower, exp);
						newSl = strictLower;
					}
				}
				return newInterval(isIntegral, newLo, newSl, newUp, newSu);
			} else {
				int signumLo = strictLower ? lower.signum() * 2 + 1 : lower
						.signum();
				int signumUp = strictUpper ? upper.signum() * 2 - 1 : upper
						.signum();

				newUp = power(upper, exp);
				newSu = strictUpper;
				newLo = power(lower, exp);
				newSl = strictLower;
				if (signumLo >= 0) {
					assert signumUp >= 0;
					// Do nothing
				} else if (signumUp <= 0) {
					assert signumLo <= 0;
					if (exp % 2 == 0) {
						newUp = power(negate(lower), exp);
						newSu = strictLower;
						newLo = power(negate(upper), exp);
						newSl = strictUpper;
					}
				} else {
					if (exp % 2 == 0) {
						Number tempUpFromLo = power(negate(lower), exp);
						Number tempUpFromUp = power(upper, exp);
						if (tempUpFromLo.compareTo(tempUpFromUp) < 0) {
							newUp = tempUpFromUp;
							newSu = strictUpper;
						} else {
							newUp = tempUpFromLo;
							newSu = strictLower;
						}
						newLo = zeroNumber;
						newSl = false;
					}
				}
				return newInterval(isIntegral, newLo, newSl, newUp, newSu);
			}
		} else {
			exp = -exp;
			if (interval.isUniversal()) {
				throw new IllegalArgumentException(
						"When the exponent number is less than zero, the interval should not contain zero");
			} else if (lower == null) {
				int signumUp = strictUpper ? upper.signum() * 2 - 1 : upper
						.signum();

				if (signumUp < 0) {
					if (exp % 2 == 0) {
						newLo = zeroNumber;
						newSl = true;
						newUp = divide(oneNumber, power(negate(upper), exp));
						newSu = strictUpper;
					} else {
						newLo = divide(oneNumber, power(upper, exp));
						newSl = strictUpper;
						newUp = zeroNumber;
						newSu = true;
					}
				} else {
					throw new IllegalArgumentException(
							"When the exponent number is less than zero, the interval should not contain zero");
				}
				return newInterval(isIntegral, newLo, newSl, newUp, newSu);
			} else if (upper == null) {
				int signumLo = strictLower ? lower.signum() * 2 + 1 : lower
						.signum();

				if (signumLo > 0) {
					newLo = zeroNumber;
					newSl = true;
					newUp = divide(oneNumber, power(lower, exp));
					newSu = strictLower;
				} else {
					throw new IllegalArgumentException(
							"When the exponent number is less than zero, the interval should not contain zero");
				}
				return newInterval(isIntegral, newLo, newSl, newUp, newSu);
			} else {
				int signumLo = strictLower ? lower.signum() * 2 + 1 : lower
						.signum();
				int signumUp = strictUpper ? upper.signum() * 2 - 1 : upper
						.signum();

				newLo = divide(oneNumber, power(upper, exp));
				newSl = strictUpper;
				newUp = divide(oneNumber, power(lower, exp));
				newSu = strictLower;
				if (signumLo > 0) {
					assert signumUp > 0;
					// Do nothing
				} else if (signumUp < 0) {
					assert signumLo < 0;
					if (exp % 2 == 0) {
						newUp = divide(oneNumber, power(negate(upper), exp));
						newSu = strictUpper;
						newLo = divide(oneNumber, power(negate(lower), exp));
						newSl = strictLower;
					}
				} else {
					throw new IllegalArgumentException(
							"When the exponent number is less than zero, the interval should not contain zero");
				}
				return newInterval(isIntegral, newLo, newSl, newUp, newSu);
			}
		}
	}

	@Override
	public Number power(Number number, int exp) {
		if (number instanceof IntegerNumber) {
			return power((IntegerNumber) number, exp);
		} else if (number instanceof RationalNumber) {
			return power((RationalNumber) number, exp);
		} else {
			throw new IllegalArgumentException("Unknown type of number: "
					+ number);
		}
	}

	@Override
	public IntegerNumber power(IntegerNumber number, int exp) {
		assert number != null;
		assert exp >= 0;
		if (exp == 0) {
			if (number.isZero())
				throw new IllegalArgumentException("0 could not power with 0.");
			else
				return oneInteger;
		}
		IntegerNumber result = oneInteger;
		IntegerNumber base = number;
		IntegerNumber e = integer(exp);
		IntegerNumber twoInt = integer(2);

		while (true) {
			if (!mod(e, twoInt).isZero()) {
				result = multiply(result, base);
				e = subtract(e, oneInteger);
				if (e.isZero())
					break;
			}
			base = multiply(base, base);
			e = divide(e, twoInt);
		}
		return result;
	}

	@Override
	public RationalNumber power(RationalNumber number, int exp) {
		IntegerNumber baseNum = integer(number.numerator());
		IntegerNumber baseDen = integer(number.denominator());
		IntegerNumber resultNum = null;
		IntegerNumber resultDen = null;

		if (exp == 0) {
			if (number.isZero())
				throw new IllegalArgumentException(
						"0.0 could not power with 0.");
			else
				return oneRational;
		}
		if (exp == 0) {
			resultNum = oneInteger;
			resultDen = oneInteger;
		} else if (exp > 0) {
			resultNum = power(baseNum, integer(exp));
			resultDen = power(baseDen, integer(exp));
		} else {
			resultNum = power(baseDen, integer(-exp));
			resultDen = power(baseNum, integer(-exp));
		}
		return fraction(resultNum, resultDen);
	}

	@Override
	public Interval singletonInterval(Number x) {
		assert x != null;
		return newInterval(x instanceof IntegerNumber, x, false, x, false);
	}

	// @Override
	public Interval restrictUpperBAD(Interval interval, Number bound,
			boolean strict) {
		assert interval != null;
		assert interval.isIntegral() == bound instanceof IntegerNumber;

		boolean isInt = interval.isIntegral();
		boolean strictUpper = interval.strictUpper();
		boolean strictLower = interval.strictLower();
		Number upper = interval.upper();
		Number lower = interval.lower();

		if (bound == null) {
			assert strict;
			return interval;
		}
		if (interval.isUniversal()) {
			return newInterval(isInt, null, true, bound, strict);
		} else if (lower == null) {
			int compareUpperBound = upper.compareTo(bound);

			if (compareUpperBound > 0) {
				return newInterval(isInt, null, true, bound, strict);
			} else if (compareUpperBound < 0) {
				return interval;
			} else {
				return newInterval(isInt, null, true, bound, strict
						|| strictUpper);
			}
		} else if (upper == null) {
			int compareLowerBound = lower.compareTo(bound);

			if (compareLowerBound < 0
					|| (compareLowerBound == 0 && !strict && !strictLower)) {
				return newInterval(isInt, lower, strictLower, bound, strict);
			} else {
				return isInt ? emptyIntegerInterval : emptyRationalInterval;
			}
		} else {
			int compareUpperBound = upper.compareTo(bound);

			if (compareUpperBound < 0) {
				return interval;
			} else if (compareUpperBound == 0) {
				return newInterval(isInt, lower, strictLower, bound, strict
						|| strictUpper);
			} else {
				int compareLowerBound = lower.compareTo(bound);

				if ((compareLowerBound < 0)
						|| (compareLowerBound == 0 && !strict && !strictLower)) {
					return newInterval(isInt, lower, strictLower, bound, strict);
				} else {
					return isInt ? emptyIntegerInterval : emptyRationalInterval;
				}
			}
		}
	}

	// @Override
	public Interval restrictLowerBAD(Interval interval, Number bound,
			boolean strict) {
		assert interval != null;
		assert interval.isIntegral() == bound instanceof IntegerNumber;

		boolean isInt = interval.isIntegral();
		boolean strictUpper = interval.strictUpper();
		boolean strictLower = interval.strictLower();
		Number upper = interval.upper();
		Number lower = interval.lower();

		if (bound == null) {
			assert strict;
			return interval;
		}
		if (interval.isUniversal()) {
			return newInterval(isInt, bound, strict, null, true);
		} else if (lower == null) {
			int compareUpperBound = upper.compareTo(bound);

			if (compareUpperBound > 0
					|| (compareUpperBound == 0 && !strict && !strictUpper)) {
				return newInterval(isInt, lower, strictLower, bound, strict);
			} else {
				return isInt ? emptyIntegerInterval : emptyRationalInterval;
			}
		} else if (upper == null) {
			int compareLowerBound = lower.compareTo(bound);

			if (compareLowerBound > 0) {
				return interval;
			} else if (compareLowerBound < 0) {
				return newInterval(isInt, bound, strict, null, true);
			} else {
				return newInterval(isInt, bound, strict || strictLower, upper,
						strictUpper);
			}
		} else {
			int compareLowerBound = lower.compareTo(bound);

			if (compareLowerBound > 0) {
				return interval;
			} else if (compareLowerBound == 0) {
				return newInterval(isInt, bound, strict || strictLower, upper,
						strictUpper);
			} else {
				int compareUpperBound = upper.compareTo(bound);

				if (compareUpperBound > 0
						|| (compareUpperBound == 0 && !strict && !strictUpper)) {
					return newInterval(isInt, bound, strict, upper, strictUpper);
				} else {
					return isInt ? emptyIntegerInterval : emptyRationalInterval;
				}
			}
		}
	}

	@Override
	public Interval join(Interval i1, Interval i2) {
		assert i1 != null && i2 != null;
		assert i1.isIntegral() == i2.isIntegral();

		boolean isInt = i1.isIntegral();
		boolean strictLower1 = i1.strictLower();
		boolean strictLower2 = i2.strictLower();
		boolean strictUpper1 = i1.strictUpper();
		boolean strictUpper2 = i2.strictUpper();
		boolean strictUpperResult = false;
		boolean strictLowerResult = false;
		Number lower1 = i1.lower();
		Number lower2 = i2.lower();
		Number upper1 = i1.upper();
		Number upper2 = i2.upper();
		Number lowerResult = null;
		Number upperResult = null;

		if (lower1 != null && lower2 != null) {
			int compareLower = lower1.compareTo(lower2);

			if (compareLower < 0) {
				strictLowerResult = strictLower1;
				lowerResult = lower1;
			} else if (compareLower > 0) {
				strictLowerResult = strictLower2;
				lowerResult = lower2;
			} else {
				strictLowerResult = strictLower1 && strictLower2;
				lowerResult = lower2;
			}
		} else {
			strictLowerResult = true;
		}
		if (upper1 != null && upper2 != null) {
			int compareUpper = upper1.compareTo(upper2);

			if (compareUpper > 0) {
				strictUpperResult = strictUpper1;
				upperResult = upper1;
			} else if (compareUpper < 0) {
				strictUpperResult = strictUpper2;
				upperResult = upper2;
			} else {
				strictUpperResult = strictUpper1 && strictUpper2;
				upperResult = upper2;
			}
		} else {
			strictUpperResult = true;
		}
		return newInterval(isInt, lowerResult, strictLowerResult, upperResult,
				strictUpperResult);
	}

	@Override
	public Interval restrictUpper(Interval interval, Number bound,
			boolean strict) {
		Interval i2 = newInterval(interval.isIntegral(), null, true, bound,
				strict);
		Interval result = intersection(interval, i2);

		return result;
	}

	@Override
	public Interval restrictLower(Interval interval, Number bound,
			boolean strict) {
		Interval i2 = newInterval(interval.isIntegral(), bound, strict, null,
				true);
		Interval result = intersection(interval, i2);

		return result;
	}

	@Override
	public IntegerNumber nthRootInt(IntegerNumber number, IntegerNumber n) {
		int nVal = n.intValue();

		if (nVal <= 0)
			throw new IllegalArgumentException(
					"The Argument 'n' to the method nthRootInt should be greater than 0."
							+ "\nThe n is: " + nVal);
		if (nVal == 1 || number.isZero() || number.isOne()
				|| negate(number).isOne())
			return number;
		if (number.signum() < 0) {
			if (nVal % 2 == 0) {
				throw new IllegalArgumentException(
						"When the argument 'number' to the method nthRootInt is negative, "
								+ "\nThe argument 'n' should be greater than 0."
								+ "\nThe n is: " + nVal);
			}
		}

		int nMinus1 = nVal - 1;
		RationalNumber nM1 = rational(integer(nMinus1));
		RationalNumber nth = divide(oneRational, rational(n));
		RationalNumber pow = rational(number);
		RationalNumber oldB = oneRational;
		RationalNumber limit = fraction(oneInteger, integer(10));
		RationalNumber newB = multiply(nth,
				add(multiply(nM1, oldB), divide(pow, power(oldB, nMinus1))));
		RationalNumber cond1 = subtract(power(subtract(newB, oldB), 2), limit);
		RationalNumber cond2 = subtract(newB, oldB);
		IntegerNumber result = null;

		while (cond1.signum() > 0 && !cond2.isZero()) {
			oldB = rational(floor(add(newB, fraction(oneInteger, integer(100)))));
			newB = multiply(nth,
					add(multiply(nM1, oldB), divide(pow, power(oldB, nMinus1))));
			newB = rational(floor(add(newB, fraction(oneInteger, integer(100)))));
			cond1 = subtract(power(subtract(newB, oldB), 2), limit);
			cond2 = subtract(newB, oldB);
		}
		newB = add(newB, fraction(oneInteger, integer(2)));
		result = floor(newB);
		if (!subtract(power(result, nVal), number).isZero()) {
			return null;
		}
		return result;
	}

	@Override
	public IntegerNumber power(IntegerNumber number, IntegerNumber exp) {
		assert number != null && exp != null;
		assert exp.signum() >= 0;
		if (exp.isZero()) {
			if (number.isZero())
				throw new IllegalArgumentException("0 could not power with 0.");
			else
				return zeroInteger;
		} else {
			IntegerNumber result = oneInteger;
			IntegerNumber base = number;
			IntegerNumber e = exp;
			IntegerNumber twoInt = integer(2);

			while (true) {
				if (!mod(e, twoInt).isZero()) {
					result = multiply(result, base);
					e = subtract(e, oneInteger);
					if (e.isZero())
						break;
				}
				base = multiply(base, base);
				e = divide(e, twoInt);
			}
			return result;
		}
	}
}
