/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.statement;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.JoinStatement;

/**
 * A join statement, to wait for another process to complete.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonJoinStatement extends CommonStatement implements
		JoinStatement {

	private Expression process;

	/**
	 * A join statement, to wait for another process to complete.
	 * 
	 * @param source
	 *            The source location for this join.
	 * @param process
	 *            A reference to the process.
	 */
	public CommonJoinStatement(Location source, Expression process) {
		super(source);
		this.process = process;
	}

	/**
	 * @return The process.
	 */
	public Expression process() {
		return process;
	}

	/**
	 * @param process
	 *            The process.
	 */
	public void setProcess(Expression process) {
		this.process = process;
	}

	@Override
	public String toString() {
		return "wait " + process;
	}

}
