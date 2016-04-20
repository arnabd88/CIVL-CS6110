package edu.udel.cis.vsl.civl.model.common.expression;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.SizeofExpressionExpression;

public class CommonSizeofExpressionExpression extends CommonExpression
		implements SizeofExpressionExpression {

	private Expression argument;

	public CommonSizeofExpressionExpression(CIVLSource source,
			Expression argument) {
		super(source);
		this.argument = argument;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.SIZEOF_EXPRESSION;
	}

	@Override
	public Expression getArgument() {
		return argument;
	}

	@Override
	public String toString() {
		return "sizeof(" + argument + ")";
	}

}
