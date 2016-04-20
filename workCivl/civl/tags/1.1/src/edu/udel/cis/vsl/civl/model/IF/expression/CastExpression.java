/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.expression;

import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;

/**
 * A cast of an expression to a different type.
 * 
 * @author zirkel
 * 
 */
public interface CastExpression extends Expression {

	/**
	 * @return The expression being cast to a new type.
	 */
	Expression getExpression();

	/**
	 * @return The type to which the expression is cast.
	 */
	CIVLType getCastType();
}
