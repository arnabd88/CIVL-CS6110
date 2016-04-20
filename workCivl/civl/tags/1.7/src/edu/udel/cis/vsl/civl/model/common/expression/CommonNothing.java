package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.Nothing;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public class CommonNothing extends CommonExpression implements Nothing {

	public CommonNothing(CIVLSource source) {
		super(source, null, null, null);
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.NOTHING;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		return null;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		return null;
	}

	@Override
	protected boolean expressionEquals(Expression expression) {
		if (expression instanceof Nothing)
			return true;
		return false;
	}

}
