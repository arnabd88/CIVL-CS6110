/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.statement;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

/**
 * A wait statement, to wait for another process to complete.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface WaitStatement extends Statement {

	/**
	 * @return The process.
	 */
	Expression process();

	/**
	 * @param process
	 *            The process.
	 */
	void setProcess(Expression process);

}
