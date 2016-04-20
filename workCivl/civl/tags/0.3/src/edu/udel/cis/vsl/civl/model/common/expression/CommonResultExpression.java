/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.expression.ResultExpression;

/**
 * This expression is only used in an ensures clause of a function contract to
 * refer to the returned value.
 * 
 * @author zirkel
 * 
 */
public class CommonResultExpression extends CommonExpression implements
		ResultExpression {

	/**
	 * This expression is only used in an ensures clause of a function contract
	 * to refer to the returned value.
	 */
	public CommonResultExpression(CIVLSource source) {
		super(source);
	}

	public String toString() {
		return "$result";
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.RESULT;
	}
}
