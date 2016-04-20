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
		// TODO Auto-generated method stub
		return null;
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
	public CallOrSpawnStatement callStatement() {
		return this.callStatement;
	}

}
