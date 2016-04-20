/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.expression.DotExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

/**
 * @author zirkel
 * 
 */
public class CommonDotExpression extends CommonExpression implements
		DotExpression {

	private Expression struct;
	private int fieldIndex;

	/**
	 * A dot expression is a reference to a field in a struct.
	 * 
	 * @param struct
	 *            The struct referenced by this dot expression.
	 * @param field
	 *            The field referenced by this dot expression.
	 */
	public CommonDotExpression(CIVLSource source, Expression struct,
			int fieldIndex) {
		super(source);
		this.struct = struct;
		this.fieldIndex = fieldIndex;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see edu.udel.cis.vsl.civl.model.IF.expression.DotExpression#struct()
	 */
	@Override
	public Expression struct() {
		return struct;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see edu.udel.cis.vsl.civl.model.IF.expression.DotExpression#field()
	 */
	@Override
	public int fieldIndex() {
		return fieldIndex;
	}

	@Override
	public String toString() {
		return struct.toString() + "." + fieldIndex;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.DOT;
	}

}
