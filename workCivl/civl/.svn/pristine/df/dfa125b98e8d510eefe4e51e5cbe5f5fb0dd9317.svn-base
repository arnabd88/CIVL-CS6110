package edu.udel.cis.vsl.civl.model.common.expression;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.expression.InitialValueExpression;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public class CommonInitialValueExpression extends CommonExpression implements
		InitialValueExpression {

	private Variable variable;

	public CommonInitialValueExpression(CIVLSource source, Variable variable) {
		super(source);
		this.variable = variable;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.INITIAL_VALUE;
	}

	@Override
	public Variable variable() {
		return variable;
	}

	@Override
	public String toString() {
		return "InitialValue(" + variable + ")";
	}

	@Override
	public void purelyLocalAnalysis() {
		this.purelyLocal = this.variable.purelyLocal();
	}
}
