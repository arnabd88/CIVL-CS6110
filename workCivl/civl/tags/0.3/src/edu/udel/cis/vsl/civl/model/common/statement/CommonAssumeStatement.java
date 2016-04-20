/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.statement;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.AssumeStatement;

/**
 * An assume statement provides an expression which is to be added to the path
 * condition.
 * 
 * @author zirkel
 * 
 */
public class CommonAssumeStatement extends CommonStatement implements
		AssumeStatement {

	private Expression expression;

	/**
	 * An assume statement.
	 * 
	 * @param source
	 *            The source location for this statement.
	 * @param expression
	 *            The expression being added to the path condition.
	 */
	public CommonAssumeStatement(CIVLSource civlSource, Location source,
			Expression expression) {
		super(civlSource, source);
		this.expression = expression;
	}

	/**
	 * @return The expression being added to the path condition.
	 */
	@Override
	public Expression getExpression() {
		return expression;
	}

	/**
	 * @param expression
	 *            The expression being added to the path condition.
	 */
	@Override
	public void setExpression(Expression expression) {
		this.expression = expression;
	}

	@Override
	public String toString() {
		return "$assume " + expression;
	}

}
