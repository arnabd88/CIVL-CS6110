package edu.udel.cis.vsl.abc.ast.node.IF.expression;

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
public interface RegularRangeNode extends ExpressionNode {

	/**
	 * Returns the lower bound argument <code>lo</code>.
	 * 
	 * @return the lower bound
	 */
	ExpressionNode getLow();

	/**
	 * Sets the lower bound argument <code>lo</code>
	 * 
	 * @param arg
	 *            the new lower bound argument
	 */
	void setLow(ExpressionNode arg);

	/**
	 * Returns the upper bound argument <code>hi</code>.
	 * 
	 * @return the lower bound
	 */
	ExpressionNode getHigh();

	/**
	 * Sets the upper bound argument <code>hi</code>
	 * 
	 * @param arg
	 *            the new upper bound argument
	 */
	void setHigh(ExpressionNode arg);

	/**
	 * Returns the step argument <code>step</code> if it is present, else
	 * returns <code>null</code>
	 * 
	 * @return the step argument or <code>null</code>
	 */
	ExpressionNode getStep();

	/**
	 * Sets the step argument <code>step</code>
	 * 
	 * @param arg
	 *            the new step argument
	 */
	void setStep(ExpressionNode arg);

}
