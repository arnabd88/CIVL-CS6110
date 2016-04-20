package edu.udel.cis.vsl.abc.ast.type.IF;

/**
 * The arithmetic types are "char", the signed and unsigned integer types,
 * enumeration types, and the floating types (which include the real and the
 * complex floating types).
 * 
 * <p>
 * The arithmetic type hierarchy can best be described by the following outline,
 * which defines a directed acyclic graph. Note that it is not a tree, as the
 * {@link IntegerType} and {@link StandardBasicType} categories have in their
 * intersection the type <code>char</code> and the
 * {@link SignedOrUnsignedIntegerType}s.
 * </p>
 * 
 * 
 * {@link UnqualifiedObjectType}
 * <ul>
 * <li>{@link ArithmeticType}
 * <ul>
 * <li>{@link IntegerType}
 * <ul>
 * <li><code>char</code></li>
 * <li>{@link EnumerationType}</li>
 * <li>{@link SignedOrUnsignedIntegerType}</li>
 * </ul>
 * </li>
 * <li>{@link StandardBasicType}
 * <ul>
 * <li><code>char</code></li>
 * <li>{@link SignedOrUnsignedIntegerType}</li>
 * <li>{@link FloatingType}</li>
 * </ul>
 * </li>
 * <ul></li>
 * </ul>
 * 
 * @author siegel
 */
public interface ArithmeticType extends UnqualifiedObjectType {

	/**
	 * Is this an integer type? Note that this includes "signed char" and
	 * "unsigned char".
	 * 
	 * This method is equivalent to isSigned() || isUnsigned, but is provided
	 * for convenience.
	 * 
	 * @return true iff this is a signed or unsigned integer type
	 */
	boolean isInteger();

	/**
	 * Is this a floating type? This includes the three real floating types and
	 * the three complex floating types. If true, this object can be safely cast
	 * to FloatingType.
	 * 
	 * @return true iff this is a floating type
	 */
	boolean isFloating();

	/**
	 * Is this an enumeration type? If true, this object can be safely cast to
	 * EnumerationType.
	 * 
	 * @return true iff this is an enumeration type
	 */
	boolean isEnumeration();

	/**
	 * Is this type in the real domain? The arithmetic types are partitioned
	 * into the real and the complex domains. The complex domain includes the
	 * three complex types. Everything else (enumerations, signed and unsigned
	 * integer types, char) falls under the real domain.
	 * 
	 * @return true iff this type is in the real domain
	 */
	boolean inRealDomain();

	/**
	 * Is this type in the complex domain? The arithmetic types are partitioned
	 * into the real and the complex domains. The complex domain includes the
	 * three complex types. Everything else (enumerations, signed and unsigned
	 * integer types, char) falls under the real domain.
	 * 
	 * @return true iff this type is in the complex domain
	 */
	boolean inComplexDomain();
}
