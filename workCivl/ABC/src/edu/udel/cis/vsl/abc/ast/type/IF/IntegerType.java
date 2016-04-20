package edu.udel.cis.vsl.abc.ast.type.IF;

/**
 * Marker interface for all "integer type" nodes. The integer types are char,
 * the signed and unsigned integer types, the enumeration types, and other
 * integer types that may be defined by an implementation.
 * 
 * Note that "char" is neither signed nor unsigned. Enumerated types are also
 * neither signed nor unsigned. All other integer types are either signed or
 * unsigned.
 * 
 * <pre>
 * | IntegerType  (e.g., wchar_t)
 * | | SignedOrUnsignedIntegerType
 * | | | SignedIntegerType (e.g., ptrdiff_t)
 * | | | | StandardSignedIntegerType (e.g., "long int")
 *         kind: SignedIntKind
 * | | | UnsignedIntegerType (e.g., size_t)
 * | | | | StandardUnsignedIntegerType (e.g., "unsigned long int")
 *         kind: UnsignedIntKind
 * | | EnumerationType
 * | | char
 * </pre>
 * 
 * Note that wchar_t may be either char or a signed or unsigned integer type.
 * 
 * @author siegel
 */
public interface IntegerType extends ArithmeticType {

}
