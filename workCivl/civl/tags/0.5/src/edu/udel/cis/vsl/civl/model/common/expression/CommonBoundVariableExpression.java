package edu.udel.cis.vsl.civl.model.common.expression;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.expression.BoundVariableExpression;

public class CommonBoundVariableExpression extends CommonExpression implements
		BoundVariableExpression {

	private Identifier name;
	
	public CommonBoundVariableExpression(CIVLSource source, Identifier name) {
		super(source);
		this.name = name;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.BOUND_VARIABLE;
	}

	@Override
	public Identifier name() {
		return name;
	}
	
	@Override
	public String toString() {
		return name.name();
	}

}
