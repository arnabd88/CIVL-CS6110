/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.statement;

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
public interface ChooseStatement extends AssignStatement {

	/**
	 * @return A unique ID for this choose.
	 */
	int chooseID();

}
