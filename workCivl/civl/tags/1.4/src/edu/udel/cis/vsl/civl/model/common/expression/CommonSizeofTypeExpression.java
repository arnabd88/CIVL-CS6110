package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.SizeofTypeExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public class CommonSizeofTypeExpression extends CommonExpression implements
		SizeofTypeExpression {

	private CIVLType type;

	public CommonSizeofTypeExpression(CIVLSource source, Scope scope,
			CIVLType myType, CIVLType type) {
		super(source, scope, scope, myType);
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

	@Override
	protected boolean expressionEquals(Expression expression) {
		// TODO Auto-generated method stub
		return false;
	}
}
