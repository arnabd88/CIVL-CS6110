package edu.udel.cis.vsl.civl.model.IF.expression;

/**
 * This represents an address-of expression, which contains one operand, and has
 * the format: <code>&x</code>, where <code>&</code> is the address-of operator
 * and <code>x</code> is the operand.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public interface AddressOfExpression extends Expression {

	/**
	 * @return The operand.
	 */
	LHSExpression operand();

}
