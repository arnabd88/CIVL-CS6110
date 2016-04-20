package edu.udel.cis.vsl.civl.model.IF.expression;

import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * This is the guard expression of CIVL for loops (<code>$for</code>). It has
 * the form of <code>(i, j, k, ... : dom)</code>, where <code>i, j, k ...</code>
 * are iteration variables and <code>dom</code> is the domain expression. The
 * number of iteration variables should be equal to the dimension of the domain.
 * A domain guard expression is evaluated to be true if and only if there exists
 * a subsequent element of <code>(i, j, k, ...)</code> in the domain.
 * 
 * @author Manchun Zheng (zmanchun)
 * */
public interface DomainGuardExpression extends Expression {

	/**
	 * Returns the domain expression.
	 * 
	 * @return The domain expression.
	 */
	Expression domain();

	/**
	 * Returns the dimension of the domain expression.
	 * 
	 * @return The dimension of the domain expression.
	 */
	int dimension();

	/**
	 * Returns the iteration variable of the given index.
	 * 
	 * @param index
	 *            The index of the iteration variable to be returned.
	 * @return The iteration variable of the given index.
	 */
	Variable variableAt(int index);

	/**
	 * The counter variable for iterating a literal domain step by step.
	 * 
	 * @return the variable expression of the counter.
	 */
	Variable getLiteralDomCounter();
}
