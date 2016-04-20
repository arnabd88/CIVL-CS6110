/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.expression.BooleanLiteralExpression;

/**
 * A literal boolean value.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonBooleanLiteralExpression extends CommonExpression implements
		BooleanLiteralExpression {

	private boolean value;

	/**
	 * A literal boolean value.
	 * 
	 * @param The
	 *            value of this boolean literal.
	 */
	public CommonBooleanLiteralExpression(CIVLSource source, boolean value) {
		super(source);
		this.value = value;
	}

	/**
	 * @return The value of this boolean literal.
	 */
	public boolean value() {
		return value;
	}

	/**
	 * @param The
	 *            value of this boolean literal.
	 */
	public void setValue(boolean value) {
		this.value = value;
	}

	@Override
	public String toString() {
		if (value) {
			return "true";
		}
		return "false";
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.BOOLEAN_LITERAL;
	}

}
