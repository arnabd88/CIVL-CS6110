/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.statement;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.ChooseStatement;

/**
 * A choose statement is of the form x = choose(n);
 * 
 * When a choose statement is executed, the left hand side will be assigned a
 * new symbolic constant. A bound on the values of that symbolic constant will
 * be added to the path condition.
 * 
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonChooseStatement extends CommonAssignStatement implements
		ChooseStatement {

	private int chooseID;

	/**
	 * A choose statement is of the form x = choose(n);
	 * 
	 * When a choose statement is executed, the left hand side will be assigned
	 * a new symbolic constant. A bound on the values of that symbolic constant
	 * will be added to the path condition.
	 * 
	 * @param source
	 *            The source location for this choose statement.
	 * @param lhs
	 *            The left hand side of the choose statement.
	 * @param argument
	 *            The argument to choose().
	 */
	public CommonChooseStatement(CIVLSource civlSource, Location source,
			LHSExpression lhs, Expression argument, int chooseID) {
		super(civlSource, source, lhs, argument);
		this.chooseID = chooseID;
	}

	@Override
	public String toString() {
		return getLhs() + " = choose(" + rhs() + ")";
	}

	/**
	 * @return A unique ID for this choose.
	 */
	@Override
	public int chooseID() {
		return chooseID;
	}
	
}
