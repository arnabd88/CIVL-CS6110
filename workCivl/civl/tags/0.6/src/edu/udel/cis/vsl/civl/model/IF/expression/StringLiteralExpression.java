/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.expression;

/**
 * A string literal.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface StringLiteralExpression extends LiteralExpression {

	/**
	 * @return The string.
	 */
	String value();

	/**
	 * @param value
	 *            The string.
	 */
	void setValue(String value);

}
