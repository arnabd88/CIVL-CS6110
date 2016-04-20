package edu.udel.cis.vsl.abc.ast.type.common;

import java.math.BigInteger;

import edu.udel.cis.vsl.abc.ast.type.IF.StandardUnsignedIntegerType;

public class CommonStandardUnsignedIntegerType extends CommonBasicType
		implements StandardUnsignedIntegerType {

	/**
	 * Minimum value for UCHAR_MAX, the maximum value for an object of type
	 * unsigned char.
	 */
	public static final BigInteger UCHAR_MAX_MIN = new BigInteger("255"); // 2^8-1

	/**
	 * Minimum value for MB_LEN_MAX, the maximum number of bytes in a multibyte
	 * character, for any supported locale.
	 */
	public static final BigInteger MB_LEN_MAX_MIN = new BigInteger("1");

	/**
	 * Minimum value for USHRT_MAX, the maximum value for an object of type
	 * unsigned short int.
	 */
	public static final BigInteger USHRT_MAX_MIN = new BigInteger("65535");// 2^16-1

	/**
	 * Minimum value for UINT_MAX, the maximum value for an object of type
	 * unsigned int.
	 */
	public static final BigInteger UINT_MAX_MIN = new BigInteger("65535"); // 2^16-1

	/**
	 * Minimum value for ULONG_MAX, the maximum value for an object of type
	 * unsigned long int.
	 */
	public static final BigInteger ULONG_MAX_MIN = new BigInteger("4294967295");// 2^32-1

	/**
	 * Minimum value for ULLONG_MAX, the maximum value for an object of type
	 * unsigned long long int.
	 */
	public static final BigInteger ULLONG_MAX_MIN = new BigInteger(
			"18446744073709551615");// 2^64-1

	private static BasicTypeKind integerToBasic(UnsignedIntKind integerTypeKind) {
		switch (integerTypeKind) {
		case BOOL:
			return BasicTypeKind.BOOL;
		case UNSIGNED_CHAR:
			return BasicTypeKind.UNSIGNED_CHAR;
		case UNSIGNED_SHORT:
			return BasicTypeKind.UNSIGNED_SHORT;
		case UNSIGNED:
			return BasicTypeKind.UNSIGNED;
		case UNSIGNED_LONG:
			return BasicTypeKind.UNSIGNED_LONG;
		case UNSIGNED_LONG_LONG:
			return BasicTypeKind.UNSIGNED_LONG_LONG;
		}
		throw new RuntimeException("Unreachable");
	}

	private UnsignedIntKind integerTypeKind;

	public CommonStandardUnsignedIntegerType(UnsignedIntKind integerTypeKind) {
		super(integerToBasic(integerTypeKind));
		this.integerTypeKind = integerTypeKind;
	}

	@Override
	public UnsignedIntKind getIntKind() {
		return integerTypeKind;
	}

	public BigInteger getMinimumMaxValue() {
		switch (integerTypeKind) {
		case UNSIGNED_CHAR:
			return UCHAR_MAX_MIN;
		case UNSIGNED_SHORT:
			return USHRT_MAX_MIN;
		case UNSIGNED:
			return UINT_MAX_MIN;
		case UNSIGNED_LONG:
			return ULONG_MAX_MIN;
		case UNSIGNED_LONG_LONG:
			return ULLONG_MAX_MIN;
		default:
			throw new RuntimeException("unreachable");
		}
	}

	@Override
	public boolean inMinimumRange(BigInteger intVal) {
		return intVal.signum() >= 0
				&& intVal.compareTo(getMinimumMaxValue()) <= 0;
	}

}
