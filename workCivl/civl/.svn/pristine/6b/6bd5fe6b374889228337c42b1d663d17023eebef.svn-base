/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.expression.ArrowExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

/**
 * @author zirkel
 * 
 */
public class CommonArrowExpression extends CommonExpression implements
		ArrowExpression {

	private Expression structPointer;
	private Identifier field;

	/**
	 * An arrow expression is a reference to a field in a struct pointer.
	 * 
	 * @param structPointer
	 *            The struct pointer referenced by this arrow expression.
	 * @param field
	 *            The field referenced by this arrow expression.
	 */
	public CommonArrowExpression(Expression structPointer, Identifier field) {
		this.structPointer = structPointer;
		this.field = field;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * edu.udel.cis.vsl.civl.model.IF.expression.ArrowExpression#structPointer()
	 */
	@Override
	public Expression structPointer() {
		return structPointer;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see edu.udel.cis.vsl.civl.model.IF.expression.ArrowExpression#field()
	 */
	@Override
	public Identifier field() {
		return field;
	}

	@Override
	public String toString() {
		return structPointer.toString() + "->" + field.toString();
	}

}
