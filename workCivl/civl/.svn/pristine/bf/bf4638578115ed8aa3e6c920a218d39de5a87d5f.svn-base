package edu.udel.cis.vsl.civl.model.common.expression;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.expression.SizeofTypeExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;

public class CommonSizeofTypeExpression extends CommonExpression implements
		SizeofTypeExpression {

	private CIVLType type;

	public CommonSizeofTypeExpression(CIVLSource source, CIVLType type) {
		super(source);
		this.type = type;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.SIZEOF_TYPE;
	}

	@Override
	public CIVLType getTypeArgument() {
		return type;
	}

	@Override
	public String toString() {
		return "sizeof(" + getTypeArgument() + ")";
	}

}
