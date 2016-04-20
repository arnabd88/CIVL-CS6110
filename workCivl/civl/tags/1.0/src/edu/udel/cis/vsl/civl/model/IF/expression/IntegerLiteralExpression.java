/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.expression;

import java.math.BigInteger;

/**
 * An integer literal.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface IntegerLiteralExpression extends LiteralExpression {

	/**
	 * @return The (arbitrary precision) value of the integer.
	 */
	BigInteger value();

	/**
	 * @param value
	 *            The (arbitrary precision) value of the integer.
	 */
	void setValue(BigInteger value);

}
