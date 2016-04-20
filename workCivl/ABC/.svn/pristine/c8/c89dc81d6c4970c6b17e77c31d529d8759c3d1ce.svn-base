package edu.udel.cis.vsl.abc.ast.value.common;

import java.math.BigInteger;

import edu.udel.cis.vsl.abc.ast.type.IF.FloatingType;
import edu.udel.cis.vsl.abc.ast.value.IF.RealFloatingValue;
import edu.udel.cis.vsl.abc.ast.value.IF.ValueFactory.Answer;

public class CommonRealFloatingValue extends CommonValue implements
		RealFloatingValue {

	private final static int classCode = CommonRealFloatingValue.class
			.hashCode();

	/**
	 * The "radix" or "base" in which the number is interpreted. Must be 10 or
	 * 16.
	 */
	private int radix;

	/**
	 * The value of the digits preceding the decimal point
	 */
	private BigInteger wholePartValue;

	/**
	 * The value of the digits following the decimal point, but excluding the
	 * exponent part.
	 */
	private BigInteger fractionPartValue;

	/**
	 * The number of digits in the fraction part.
	 */
	private int fractionLength;

	/**
	 * The value of the exponent.
	 */
	private BigInteger exponentValue;

	public CommonRealFloatingValue(FloatingType type, int radix,
			BigInteger wholePartValue, BigInteger fractionPartValue,
			int fractionLength, BigInteger exponentValue) {
		super(type);
		assert wholePartValue != null;
		assert fractionPartValue != null;
		assert exponentValue != null;
		this.radix = radix;
		this.wholePartValue = wholePartValue;
		this.fractionPartValue = fractionPartValue;
		this.fractionLength = fractionLength;
		this.exponentValue = exponentValue;
	}

	@Override
	public FloatingType getType() {
		return (FloatingType) super.getType();
	}

	@Override
	public int getRadix() {
		return radix;
	}

	@Override
	public double getDoubleValue() {
		double result = wholePartValue.doubleValue();

		if (radix == 16) {
			result += fractionPartValue.doubleValue()
					* Math.pow(2, -4 * fractionLength);
			result *= Math.pow(2, exponentValue.doubleValue());
		} else if (radix == 10) {
			result += fractionPartValue.doubleValue()
					* Math.pow(10, -fractionLength);
			result *= Math.pow(10, exponentValue.doubleValue());
		} else {
			throw new RuntimeException("Only know base 10 and 16");
		}
		return result;
	}

	@Override
	public BigInteger getWholePartValue() {
		return wholePartValue;
	}

	@Override
	public BigInteger getFractionPartValue() {
		return fractionPartValue;
	}

	@Override
	public int getFractionLength() {
		return fractionLength;
	}

	@Override
	public BigInteger getExponentValue() {
		return exponentValue;
	}

	@Override
	public boolean equals(Object object) {
		if (this == object)
			return true;
		if (this instanceof CommonRealFloatingValue) {
			CommonRealFloatingValue that = (CommonRealFloatingValue) object;

			return getType().equals(that.getType())
					&& exponentValue.equals(that.exponentValue)
					&& fractionPartValue.equals(that.fractionPartValue)
					&& fractionLength == that.fractionLength
					&& radix == that.radix
					&& wholePartValue.equals(that.wholePartValue);
		}
		return false;
	}

	@Override
	public int hashCode() {
		return classCode + getType().hashCode() + exponentValue.hashCode()
				+ fractionLength + fractionPartValue.hashCode() + radix
				+ wholePartValue.hashCode();
	}

	@Override
	public Answer isZero() {
		return wholePartValue.signum() == 0 && fractionPartValue.signum() == 0 ? Answer.YES
				: Answer.NO;
	}

	@Override
	public String toString() {
		return "FloatingConstant[radix=" + radix + ", wholePart="
				+ wholePartValue + ", fractionPart=" + fractionPartValue
				+ ", fractionLength=" + fractionLength + ", exponent="
				+ exponentValue + ", doubleValue=" + getDoubleValue() + "]";
	}

}
