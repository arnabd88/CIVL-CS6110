package edu.udel.cis.vsl.civl.model.IF.expression;

import edu.udel.cis.vsl.civl.model.IF.Identifier;

/**
 * A reference to a field in a struct pointer.  i.e. s->f in C.
 * 
 * @author zirkel
 *
 */
public interface ArrowExpression extends Expression {

	/**
	 * 
	 * @return The struct pointer referenced by this arrow expression.
	 */
	public Expression structPointer();
	
	/**
	 * 
	 * @return The field referenced by this arrow expression.
	 */
	public Identifier field();
	
}
