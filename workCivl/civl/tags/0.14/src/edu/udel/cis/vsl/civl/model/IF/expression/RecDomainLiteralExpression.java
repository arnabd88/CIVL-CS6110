package edu.udel.cis.vsl.civl.model.IF.expression;

/**
 * This is a rectangular domain literal expression, which is the Cartesian
 * product of a number of ranges, e.g.,
 * <code>{range1, range2, range3, ...}</code>.
 * 
 * @author Manchun Zheng
 *
 */
public interface RecDomainLiteralExpression extends LiteralExpression {

	/**
	 * Returns the range expression of the domain literal at the given index.
	 * 
	 * @param index
	 *            The index of the range to be returned.
	 * @return The range expression of the domain literal at the given index.
	 */
	Expression rangeAt(int index);

	/**
	 * Returns the dimension of this domain literal, which is equal to the
	 * number of ranges.
	 * 
	 * @return The dimension of this domain literal, which is equal to the
	 *         number of ranges.
	 */
	int dimension();
}
