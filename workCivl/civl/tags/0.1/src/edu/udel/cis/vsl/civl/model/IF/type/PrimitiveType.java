 package edu.udel.cis.vsl.civl.model.IF.type;

/**
 * A primitive type. One of: int, bool, real, string.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface PrimitiveType extends Type {

	public enum PRIMITIVE_TYPE {
		INT, BOOL, REAL, STRING
	};

	/**
	 * @return The actual primitive type (int, bool, real, or string).
	 */
	public PRIMITIVE_TYPE primitiveType();

	/**
	 * @param The
	 *            actual primitive type (int, bool, real, or string).
	 */
	public void setPrimitiveType(PRIMITIVE_TYPE primitiveType);

}
