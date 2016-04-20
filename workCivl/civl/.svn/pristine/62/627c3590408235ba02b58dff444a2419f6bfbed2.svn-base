/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.expression.DynamicTypeOfExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;

/**
 * A cast of an expression to a different type.
 * 
 * @author zirkel
 * 
 */
public class CommonDynamicTypeOfExpression extends CommonExpression implements
		DynamicTypeOfExpression {

	private CIVLType type;

	public CommonDynamicTypeOfExpression(CIVLSource source, CIVLType type) {
		super(source);
		this.type = type;
	}

	@Override
	public CIVLType getType() {
		return type;
	}

	@Override
	public String toString() {
		return "DynamicTypeOf(" + type + ") ";
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.DYNAMIC_TYPE_OF;
	}

}
