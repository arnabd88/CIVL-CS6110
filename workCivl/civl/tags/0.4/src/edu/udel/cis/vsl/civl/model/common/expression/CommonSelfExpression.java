/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.expression.SelfExpression;

/**
 * Self expression. Returns a reference to the process in which the expression
 * is evaluated.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonSelfExpression extends CommonExpression implements
		SelfExpression {

	/**
	 * Self expression. Returns a reference to the process in which the
	 * expression is evaluated.
	 */
	public CommonSelfExpression(CIVLSource source) {
		super(source);
	}

	@Override
	public String toString() {
		return "$self";
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.SELF;
	}
}
