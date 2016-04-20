/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.expression.UndefinedProcessExpression;

/**
 * Self expression. Returns a reference to the process in which the expression
 * is evaluated.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonUndefinedProcessExpression extends CommonExpression
		implements UndefinedProcessExpression {

	/**
	 * Self expression. Returns a reference to the process in which the
	 * expression is evaluated.
	 */
	public CommonUndefinedProcessExpression(CIVLSource source) {
		super(source);
	}

	@Override
	public String toString() {
		return "process<-1>";
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.UNDEFINED_PROC;
	}
}
