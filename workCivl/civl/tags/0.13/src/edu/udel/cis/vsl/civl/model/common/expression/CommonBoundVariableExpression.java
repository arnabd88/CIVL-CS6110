package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.BoundVariableExpression;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

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

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		// TODO Auto-generated method stub
		return null;
	}

}
