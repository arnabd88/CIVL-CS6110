package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.SystemFunctionCallExpression;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public class CommonSystemFunctionCallExpression extends CommonExpression
		implements SystemFunctionCallExpression {

	CallOrSpawnStatement callStatement;

	public CommonSystemFunctionCallExpression(CIVLSource source,
			CallOrSpawnStatement callStatement) {
		super(source);
		this.callStatement = callStatement;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.SYSTEM_FUNC_CALL;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		return callStatement.variableAddressedOf(scope);
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		return callStatement.variableAddressedOf();
	}

	@Override
	public CallOrSpawnStatement callStatement() {
		return this.callStatement;
	}

	@Override
	public String toString() {
		return this.callStatement.toString();
	}
}
