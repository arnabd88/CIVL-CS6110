/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.expression;

import java.math.BigDecimal;

/**
 * A real literal.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface RealLiteralExpression extends LiteralExpression {

	/**
	 * @return The (arbitrary precision) real value.
	 */
	public BigDecimal value();

	/**
	 * @param value
	 *            The (arbitrary precision) real value.
	 */
	public void setValue(BigDecimal value);
	
}
