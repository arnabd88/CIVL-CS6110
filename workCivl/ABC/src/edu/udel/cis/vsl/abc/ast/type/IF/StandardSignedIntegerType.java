package edu.udel.cis.vsl.abc.ast.type.IF;

import java.math.BigInteger;

/**
 * The 5 "standard" signed integer types.
 * 
 * There are 5 standard signed types and 6 standard unsigned types (as BOOL
 * exists only in unsigned form).
 * 
 * 
 * The set of standard signed or unsigned integer types is a subset of the set
 * of standard basic types, so the information provided by this interface is
 * redundant---it is completely determined by the basic type kind. However, in
 * some situations it is convenient to use this view of the information.
 * 
 * @author siegel
 * 
 */
public interface StandardSignedIntegerType extends SignedIntegerType,
		StandardBasicType {

	/**
	 * The 5 kinds of standard signed integer types. The names are the same as
	 * those using in BasicTypeKind.
	 * 
	 */
	public static enum SignedIntKind {
		SIGNED_CHAR, SHORT, INT, LONG, LONG_LONG
	};

	/**
	 * Returns the kind of standard signed integer
	 * 
	 * @return the kind of standard signed integer
	 */
	SignedIntKind getIntKind();

	/**
	 * The minimum greatest integer in this type
	 * 
	 * @return minimum greatest integer in this type
	 */
	BigInteger getMinimumMaxValue();

	/**
	 * The minimum <b>absolute value</b> of the least integer in this type.
	 * 
	 * @return minimum <b>absolute value</b> of the least integer in this type
	 */
	BigInteger getMinimumMinValue();

	/**
	 * Is -m <= x <= M, where m=getMinimumMinValue(), M=getMinimumMaxValue.
	 * 
	 * @param intVal
	 * @return <code>true</code> iff -m <= x <= M
	 */
	boolean inMinimumRange(BigInteger intVal);
}
