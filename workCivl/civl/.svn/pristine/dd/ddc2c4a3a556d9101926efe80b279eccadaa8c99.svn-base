package edu.udel.cis.vsl.civl.model.IF.statement;

import java.util.List;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;

/**
 * <p>
 * Represents the enter statement of a CIVL <code>$for</code>.
 * </p>
 * 
 * @author Manchun Zheng (zmanchun)
 */
public interface CivlForEnterStatement extends Statement {

	/**
	 * Returns the iteration domain expression, which is the expression
	 * following the colon.
	 * 
	 * @return the iteration domain expression
	 */
	Expression domain();

	/**
	 * Returns the list of loop variables, ordered from left to right.
	 * 
	 * @return the list of loop variables
	 */
	List<VariableExpression> loopVariables();
}
