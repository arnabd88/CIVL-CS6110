package edu.udel.cis.vsl.abc.config.common;

import java.math.BigInteger;

import edu.udel.cis.vsl.abc.config.IF.Configuration;

public class CommonConfiguration implements Configuration {

	private boolean svcomp = false;

	private Architecture architecture = Architecture.UNKNOWN;

	/** number of bits for smallest object that is not a bit-field (byte) */
	BigInteger CHAR_BIT = new BigInteger("8");

	/** minimum value for an object of type signed char */
	BigInteger SCHAR_MIN = new BigInteger("-127"); // -(2^7-1)

	/** maximum value for an object of type signed char */
	BigInteger SCHAR_MAX = new BigInteger("127"); // 2^7-1

	/** maximum value for an object of type unsigned char */
	BigInteger UCHAR_MAX = new BigInteger("255"); // 2^8-1

	/** minimum value for an object of type char */
	BigInteger CHAR_MIN = SCHAR_MIN;

	/** maximum value for an object of type char */
	BigInteger CHAR_MAX = SCHAR_MAX;

	/**
	 * maximum number of bytes in a multibyte character, for any supported
	 * locale
	 */
	BigInteger MB_LEN_MAX = new BigInteger("1");

	/** minimum value for an object of type short int */
	BigInteger SHRT_MIN = new BigInteger("-32767"); // -(2^15-1);

	/** maximum value for an object of type short int */
	BigInteger SHRT_MAX = new BigInteger("32767"); // 2^15-1

	/** maximum value for an object of type unsigned short int */
	BigInteger USHRT_MAX = new BigInteger("65535");// 2^16-1

	/** minimum value for an object of type int */
	BigInteger INT_MIN = new BigInteger("-32767"); // -(215-1)

	/** maximum value for an object of type int */
	BigInteger INT_MAX = new BigInteger("32767"); // 215-1

	/** maximum value for an object of type unsigned int */
	BigInteger UINT_MAX = new BigInteger("65535"); // 2^16-1

	/** minimum value for an object of type long int */
	BigInteger LONG_MIN = new BigInteger("-2147483647");// -(2^31-1)

	/** maximum value for an object of type long int */
	BigInteger LONG_MAX = new BigInteger("2147483647");// 2^31-1

	/** maximum value for an object of type unsigned long int */
	BigInteger ULONG_MAX = new BigInteger("4294967295");// 2^32-1

	/** minimum value for an object of type long long int */
	BigInteger LLONG_MIN = new BigInteger("-9223372036854775807");// -(2^63-1)

	/** maximum value for an object of type long long int */
	BigInteger LLONG_MAX = new BigInteger("9223372036854775807");// 2^63-1

	/** maximum value for an object of type unsigned long long int */
	BigInteger ULLONG_MAX = new BigInteger("18446744073709551615");// 2^64-1

	@Override
	public BigInteger unsignedCharMax() {
		return UCHAR_MAX;
	}

	@Override
	public BigInteger unsignedShortIntMax() {
		return USHRT_MAX;
	}

	@Override
	public BigInteger unsignedIntMax() {
		return UINT_MAX;
	}

	@Override
	public BigInteger unsignedLongIntMax() {
		return ULONG_MAX;
	}

	@Override
	public BigInteger unsignedLongLongIntMax() {
		return ULLONG_MAX;
	}

	@Override
	public BigInteger signedCharMin() {
		return SCHAR_MIN;
	}

	@Override
	public BigInteger signedCharMax() {
		return SCHAR_MAX;
	}

	@Override
	public BigInteger signedShortIntMin() {
		return SHRT_MIN;
	}

	@Override
	public BigInteger signedShortIntMax() {
		return SHRT_MAX;
	}

	@Override
	public BigInteger signedIntMin() {
		return INT_MIN;
	}

	@Override
	public BigInteger signedIntMax() {
		return INT_MAX;
	}

	@Override
	public BigInteger signedLongIntMin() {
		return LONG_MIN;
	}

	@Override
	public BigInteger signedLongIntMax() {
		return LONG_MAX;
	}

	@Override
	public BigInteger signedLongLongIntMin() {
		return LLONG_MIN;
	}

	@Override
	public BigInteger signedLongLongIntMax() {
		return LLONG_MAX;
	}

	public boolean inRangeUnsignedChar(BigInteger value) {
		return value.compareTo(unsignedCharMax()) <= 0;
	}

	public boolean inRangeUnsignedShort(BigInteger value) {
		return value.compareTo(unsignedShortIntMax()) <= 0;
	}

	public boolean inRangeUnsignedInt(BigInteger value) {
		return value.compareTo(unsignedIntMax()) <= 0;
	}

	public boolean inRangeUnsignedLongInt(BigInteger value) {
		return value.compareTo(unsignedLongIntMax()) <= 0;
	}

	public boolean inRangeUnsignedLongLongInt(BigInteger value) {
		return value.compareTo(unsignedLongLongIntMax()) <= 0;
	}

	public boolean inRangeSignedChar(BigInteger value) {
		return value.compareTo(signedCharMin()) >= 0
				&& value.compareTo(signedCharMax()) <= 0;
	}

	public boolean inRangeSignedShort(BigInteger value) {
		return value.compareTo(signedShortIntMin()) >= 0
				&& value.compareTo(signedShortIntMax()) <= 0;
	}

	public boolean inRangeSignedInt(BigInteger value) {
		return value.compareTo(signedIntMin()) >= 0
				&& value.compareTo(signedIntMax()) <= 0;
	}

	public boolean inRangeSignedLongInt(BigInteger value) {
		return value.compareTo(signedLongIntMin()) >= 0
				&& value.compareTo(signedLongIntMax()) <= 0;
	}

	public boolean inRangeSignedLongLongInt(BigInteger value) {
		return value.compareTo(signedLongLongIntMin()) >= 0
				&& value.compareTo(signedLongLongIntMax()) <= 0;
	}

	@Override
	public BigInteger charMin() {
		return signedCharMin();
	}

	@Override
	public BigInteger charMax() {
		return signedCharMax();
	}

	@Override
	public boolean svcomp() {
		return this.svcomp;
	}

	@Override
	public void setSvcomp(boolean svcomp) {
		this.svcomp = svcomp;
	}

	@Override
	public void setArchitecture(Architecture arch) {
		this.architecture = arch;
	}

	@Override
	public Architecture architecture() {
		return this.architecture;
	}

}
