/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.statement;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.ReturnStatement;

/**
 * A return statement.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonReturnStatement extends CommonStatement implements
		ReturnStatement {

	private Expression expression;

	/**
	 * A return statement.
	 * 
	 * @param source
	 *            The source location for this return statement.
	 * @param expression
	 *            The expression being returned. Null if non-existent.
	 */
	public CommonReturnStatement(CIVLSource civlSource, Location source,
			Expression expression) {
		super(civlSource, source);
		this.expression = expression;
	}

	/**
	 * @return The expression being returned. Null if non-existent.
	 */
	@Override
	public Expression expression() {
		return expression;
	}

	/**
	 * @param expression
	 *            The expression being returned. Null if non-existent.
	 */
	@Override
	public void setExpression(Expression expression) {
		this.expression = expression;
	}

	@Override
	public String toString() {
		if (expression == null) {
			return "return";
		}
		return "return " + expression;
	}

}
