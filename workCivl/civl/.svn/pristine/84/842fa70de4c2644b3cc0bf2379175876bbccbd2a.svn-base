package edu.udel.cis.vsl.civl.model.IF.expression;

/**
 * This class represents a pointer set P. P is expressed as a base pointer p and
 * a set of offsets f. p shall be a {@link LHSExpression} and f shall be either
 * a integer number or a range with step 1.
 * 
 * @author ziqingluo
 *
 */
public interface PointerSetExpression extends Expression {
	/**
	 * Get the base pointer
	 * 
	 * @return
	 */
	LHSExpression getBasePointer();

	/**
	 * Get the range which represents a set of offsets.
	 * 
	 * @return
	 */
	Expression getRange();
}
