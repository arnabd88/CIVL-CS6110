package edu.udel.cis.vsl.abc.ast.type.common;

import java.math.BigInteger;

import edu.udel.cis.vsl.abc.ast.type.IF.StandardSignedIntegerType;

public class CommonStandardSignedIntegerType extends CommonBasicType implements
		StandardSignedIntegerType {

	/**
	 * Minimum (in magnitude) value for SCHAR_MIN, the minimum value of an
	 * object of type signed char.
	 */
	public static final BigInteger SCHAR_MIN_MIN = new BigInteger("-127"); // -(2^7-1)

	/**
	 * Minimum value for SCHAR_MAX, the maximum value for an object of type
	 * signed char.
	 */
	public static final BigInteger SCHAR_MAX_MIN = new BigInteger("127"); // 2^7-1

	/**
	 * Minimum value (in magnitude) for SHRT_MIN, the minimum value for an
	 * object of type short int.
	 */
	public static final BigInteger SHRT_MIN_MIN = new BigInteger("-32767"); // -(2^15-1);

	/**
	 * Minimum value for SHRT_MAX, the maximum value for an object of type short
	 * int.
	 */
	public static final BigInteger SHRT_MAX_MIN = new BigInteger("32767"); // 2^15-1

	/**
	 * Minimum value (in magnitude) for INT_MIN, the minimum value for an object
	 * of type int.
	 */
	public static final BigInteger INT_MIN_MIN = new BigInteger("-32767"); // -(215-1)

	/** Minimum value for INT_MAX, the maximum value for an object of type int. */
	public static final BigInteger INT_MAX_MIN = new BigInteger("32767"); // 215-1

	/**
	 * Minimum value (in magnitude) for LONG_MIN, the minimum value for an
	 * object of type long int.
	 */
	public static final BigInteger LONG_MIN_MIN = new BigInteger("-2147483647");// -(2^31-1)

	/**
	 * Minimum value for LONG_MAX, the maximum value for an object of type long
	 * int.
	 */
	public static final BigInteger LONG_MAX_MIN = new BigInteger("2147483647");// 2^31-1

	/**
	 * Minimum value (in magnitude) for LLONG_MIN, the minimum value for an
	 * object of type long long int.
	 */
	public static final BigInteger LLONG_MIN_MIN = new BigInteger(
			"-9223372036854775807");// -(2^63-1)

	/**
	 * Minimum value for LLONG_MAX, the maximum value for an object of type long
	 * long int.
	 */
	public static final BigInteger LLONG_MAX_MIN = new BigInteger(
			"9223372036854775807");// 2^63-1

	private static BasicTypeKind integerToBasic(SignedIntKind integerTypeKind) {
		switch (integerTypeKind) {
		case SIGNED_CHAR:
			return BasicTypeKind.SIGNED_CHAR;
		case SHORT:
			return BasicTypeKind.SHORT;
		case INT:
			return BasicTypeKind.INT;
		case LONG:
			return BasicTypeKind.LONG;
		case LONG_LONG:
			return BasicTypeKind.LONG_LONG;
		}
		throw new RuntimeException("Unreachable");
	}

	private SignedIntKind integerTypeKind;

	public CommonStandardSignedIntegerType(SignedIntKind integerTypeKind) {
		super(integerToBasic(integerTypeKind));
		this.integerTypeKind = integerTypeKind;
	}

	@Override
	public SignedIntKind getIntKind() {
		return integerTypeKind;
	}

	@Override
	public BigInteger getMinimumMaxValue() {
		switch (integerTypeKind) {
		case SIGNED_CHAR:
			return SCHAR_MAX_MIN;
		case SHORT:
			return SHRT_MAX_MIN;
		case INT:
			return INT_MAX_MIN;
		case LONG:
			return LONG_MAX_MIN;
		case LONG_LONG:
			return LLONG_MAX_MIN;
		default:
			throw new RuntimeException("unreachable");
		}
	}

	@Override
	public BigInteger getMinimumMinValue() {
		switch (integerTypeKind) {
		case SIGNED_CHAR:
			return SCHAR_MIN_MIN;
		case SHORT:
			return SHRT_MIN_MIN;
		case INT:
			return INT_MIN_MIN;
		case LONG:
			return LONG_MIN_MIN;
		case LONG_LONG:
			return LLONG_MIN_MIN;
		default:
			throw new RuntimeException("unreachable");
		}
	}

	@Override
	public boolean inMinimumRange(BigInteger intVal) {
		return intVal.compareTo(getMinimumMinValue()) >= 0
				&& intVal.compareTo(getMinimumMaxValue()) <= 0;
	}
}
