/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.expression;

/**
 * A literal boolean value.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface BooleanLiteralExpression extends LiteralExpression {

	/**
	 * @return The value of this boolean literal.
	 */
	boolean value();
}
