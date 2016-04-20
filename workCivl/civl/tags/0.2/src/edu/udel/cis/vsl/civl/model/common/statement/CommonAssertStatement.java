/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.statement;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.AssertStatement;

/**
 * An assert statement.
 * 
 * @author zirkel
 * 
 */
public class CommonAssertStatement extends CommonStatement implements AssertStatement {

	private boolean isCollective = false;
	private Expression expression;

	/**
	 * @param source
	 *            The source location for this statement.
	 * @param expression
	 *            The expression being checked.
	 */
	public CommonAssertStatement(Location source, Expression expression) {
		super(source);
		this.expression = expression;
	}

	/**
	 * @return Whether this is a collective assertion.
	 */
	public boolean isCollective() {
		return isCollective;
	}

	/**
	 * @return The expression being checked.
	 */
	public Expression getExpression() {
		return expression;
	}

	/**
	 * @param isCollective
	 *            Whether this is a collective assertion.
	 */
	public void setCollective(boolean isCollective) {
		this.isCollective = isCollective;
	}

	/**
	 * @param expression
	 *            The expression being checked.
	 */
	public void setExpression(Expression expression) {
		this.expression = expression;
	}
	
	@Override
	public String toString() {
		return "$assert " + expression;
	}

}
