package edu.udel.cis.vsl.abc.ast.type.IF;

public interface QualifiedObjectType extends ObjectType {

	UnqualifiedObjectType getBaseType();

	/**
	 * Is this a "const" qualified type?
	 * 
	 * @return true iff this is a const qualified type.
	 */
	boolean isConstQualified();

	/**
	 * Is this a "volatile" qualified type?
	 * 
	 * @return true iff this is a volatile qualified type.
	 */
	boolean isVolatileQualified();

	/**
	 * Is this a "restrict" qualified type?
	 * 
	 * @return true iff this is a "restrict" qualified type.
	 */
	boolean isRestrictQualified();

	/**
	 * Is this an "_input" qualified type?
	 * 
	 * @return true iff this is an "_input" qualified type
	 */
	boolean isInputQualified();

	/**
	 * Is this an "_output" qualified type?
	 * 
	 * @return true iff this is an "_output" qualified type
	 */
	boolean isOutputQualified();

}
