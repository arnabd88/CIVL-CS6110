package edu.udel.cis.vsl.abc.ast.type.IF;

/**
 * An instance of this class represents a "standard basic type". The standard
 * basic types are: the "char" type, the standard signed and unsigned integer
 * types, and the floating types. See C11 Sec. 6.2.5 for the definition of
 * "basic type".
 * 
 * Sec. 6.7.2 of the C11 Standard covers "type specifiers". Each standard basic
 * type is specified by a sequence of type specifiers. The order in which these
 * specifiers appear does not matter, but the multiplicity does (e.g.
 * "long long int" specifies a different type than "long int"). Hence the
 * sequence may be thought of as a multiset (set with multiplicity). This is the
 * way it is described in the Standard.
 * 
 * A standard basic type may have more than one multiset that specifies it. For
 * example "long" and "long int" specify the same type.
 * 
 * The basic multisets comprise the following elements, with multiplicity:
 * 
 * char, short, int, long, float, double, signed, unsigned, bool, complex.
 * 
 * The allowable multisets are defined in C11 Sec. 6.7.2.2, and are as follows.
 * For a line with more than one multiset, each multiset on the line specifies
 * the same type.
 * 
 * <pre>
 * - char
 * - signed char
 * - unsigned char
 * - short, signed short, short int, or signed short int
 * - unsigned short, or unsigned short int
 * - int, signed, or signed int
 * - unsigned, or unsigned int
 * - long, signed long, long int, or signed long int
 * - unsigned long, or unsigned long int
 * - long long, signed long long, long long int, or signed long long int
 * - unsigned long long, or unsigned long long int
 * - float
 * - double
 * - long double
 * - _Bool
 * - float _Complex
 * - double _Complex
 * - long double _Complex
 * </pre>
 * 
 * @author siegel
 */
public interface StandardBasicType extends ArithmeticType {

	public static enum BasicTypeKind {
		BOOL,
		CHAR,
		DOUBLE,
		DOUBLE_COMPLEX,
		FLOAT,
		FLOAT_COMPLEX,
		INT,
		LONG,
		LONG_DOUBLE,
		LONG_DOUBLE_COMPLEX,
		LONG_LONG,
		REAL,
		SHORT,
		SIGNED_CHAR,
		UNSIGNED,
		UNSIGNED_CHAR,
		UNSIGNED_LONG,
		UNSIGNED_LONG_LONG,
		UNSIGNED_SHORT
	};

	/**
	 * Returns the basic type kind.
	 * 
	 * @return the basic type kind
	 */
	BasicTypeKind getBasicTypeKind();

}
