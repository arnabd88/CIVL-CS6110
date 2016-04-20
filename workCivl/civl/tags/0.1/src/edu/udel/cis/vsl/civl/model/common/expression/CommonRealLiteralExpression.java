/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import java.math.BigDecimal;

import edu.udel.cis.vsl.civl.model.IF.expression.RealLiteralExpression;

/**
 * A real literal.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonRealLiteralExpression extends CommonExpression implements
		RealLiteralExpression {

	private BigDecimal value;

	/**
	 * A real literal.
	 * 
	 * @param value
	 *            The (arbitrary precision) real value.
	 */
	public CommonRealLiteralExpression(BigDecimal value) {
		this.value = value;
	}

	/**
	 * @return The (arbitrary precision) real value.
	 */
	public BigDecimal value() {
		return value;
	}

	/**
	 * @param value
	 *            The (arbitrary precision) real value.
	 */
	public void setValue(BigDecimal value) {
		this.value = value;
	}

	@Override
	public String toString() {
		return value.toString();
	}

}
