package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.RemoteExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public class CommonRemoteExpression extends CommonExpression implements
		RemoteExpression {

	private Expression process;

	private Expression expression;

	public CommonRemoteExpression(CIVLSource source, Scope hscope,
			Scope lscope, CIVLType type, Expression expression,
			Expression process) {
		super(source, hscope, lscope, type);
		this.process = process;
		this.expression = expression;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.REMOTE_REFERENCE;
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
	public Expression process() {
		return process;
	}

	@Override
	public Expression expression() {
		return expression;
	}

	@Override
	protected boolean expressionEquals(Expression expression) {
		if (expression instanceof RemoteExpression) {
			RemoteExpression remoteExpr = (RemoteExpression) expression;

			if (!process.equals(remoteExpr.process()))
				return false;
			if (!expression.equals(remoteExpr.expression()))
				return false;
			else
				return true;
		}
		return false;
	}

	@Override
	public String toString() {
		return expression.toString() + "@" + process.toString();
	}
}
