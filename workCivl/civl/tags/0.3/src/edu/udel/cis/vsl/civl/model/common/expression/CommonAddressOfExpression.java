package edu.udel.cis.vsl.civl.model.common.expression;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.expression.AddressOfExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;

public class CommonAddressOfExpression extends CommonExpression implements
		AddressOfExpression {

	private LHSExpression operand;

	public CommonAddressOfExpression(CIVLSource source, LHSExpression operand) {
		super(source);
		this.operand = operand;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.ADDRESS_OF;
	}

	@Override
	public LHSExpression operand() {
		return operand;
	}

	@Override
	public String toString() {
		return "&" + operand;
	}

}
