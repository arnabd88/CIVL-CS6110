/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.expression;

/**
 * A dot expression is a reference to a field in a struct.
 * 
 * @author zirkel
 * 
 */
public interface DotExpression extends LHSExpression {

	/**
	 * @return The struct referenced by this dot expression.
	 */
	Expression struct();

	/**
	 * @return Index of the field referenced by this dot expression.
	 */
	int fieldIndex();
}
