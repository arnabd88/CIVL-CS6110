package edu.udel.cis.vsl.civl.model.IF.expression;

/**
 * Represents a CIVL-C regular range expression, which has the form
 * <code>lo .. hi</code> or <code>lo .. hi # step</code>.
 * 
 * <p>
 * The <code>step</code> argument is optional. If absent, it is the same as
 * using <code>1</code>.
 * </p>
 * 
 * <p>
 * If <code>step</code> is positive, it represents the sequence of integers
 * <code>lo</code>, <code>lo+step</code>, <code>lo+2*step</code>, ..., which is
 * truncated so that all entries are less than or equal to <code>hi</code>.
 * </p>
 * 
 * <p>
 * If <code>step</code> is negative</code>, it represents the sequence
 * <code>hi</code>, <code>hi</code>+<code>step</code>, <code>hi</code>+2*
 * <code>step</code>, ..., which is truncated so that all entries are greater
 * than or equal to <code>lo</code>.
 * </p>
 * 
 * @author siegel
 * 
 */
public interface RegularRangeExpression extends Expression {

	/**
	 * Returns the lower bound argument <code>lo</code>.
	 * 
	 * @return the lower bound
	 */
	Expression getLow();

	/**
	 * Returns the upper bound argument <code>hi</code>.
	 * 
	 * @return the lower bound
	 */
	Expression getHigh();

	/**
	 * Returns the step argument <code>step</code> if it is present, else
	 * returns <code>null</code>
	 * 
	 * @return the step argument or <code>null</code>
	 */
	Expression getStep();
}
