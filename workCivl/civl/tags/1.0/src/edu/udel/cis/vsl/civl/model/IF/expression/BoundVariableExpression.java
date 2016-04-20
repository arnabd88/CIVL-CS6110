package edu.udel.cis.vsl.civl.model.IF.expression;

import edu.udel.cis.vsl.civl.model.IF.Identifier;

/**
 * A bound variable is a variable used in a quantified expression.
 * 
 * @author zirkel
 *
 */
public interface BoundVariableExpression extends Expression {

	/**
	 * @return The name of this bound variable.
	 */
	Identifier name();
	
}
