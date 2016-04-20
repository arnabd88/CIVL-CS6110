package edu.udel.cis.vsl.abc.ast.type.IF;

import java.math.BigInteger;

public interface StandardUnsignedIntegerType extends UnsignedIntegerType {

	public static enum UnsignedIntKind {
		BOOL,
		UNSIGNED_CHAR,
		UNSIGNED_SHORT,
		UNSIGNED,
		UNSIGNED_LONG,
		UNSIGNED_LONG_LONG
	};

	UnsignedIntKind getIntKind();

	/**
	 * The minimum greatest value of this type. Any conforming C implementation
	 * must have a greatest value of at least this number for the given kind of
	 * type.
	 * 
	 * @return intVal minimum greatest value of this type
	 */
	BigInteger getMinimumMaxValue();

	/**
	 * Is 0 <= intVal <= getMinimumMaxValue() ?
	 * 
	 * @param intVal
	 * @return true iff intVal is in the range [0,getMinimumMaxValue()]
	 */
	boolean inMinimumRange(BigInteger intVal);

}
