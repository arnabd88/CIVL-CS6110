/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.expression;

import edu.udel.cis.vsl.civl.model.IF.Identifier;

/**
 * A dot expression is a reference to a field in a struct.
 * 
 * @author zirkel
 * 
 */
public interface DotExpression extends Expression {

	/**
	 * @return The struct referenced by this dot expression.
	 */
	Expression struct();

	/**
	 * @return The field referenced by this dot expression.
	 */
	Identifier field();
}
