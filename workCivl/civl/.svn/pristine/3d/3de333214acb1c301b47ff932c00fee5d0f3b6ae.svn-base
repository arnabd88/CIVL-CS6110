package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.ProcnullExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

public class CommonProcnullExpression extends CommonExpression implements
		ProcnullExpression {

	public CommonProcnullExpression(CIVLSource source, CIVLType type,
			SymbolicExpression constantValue) {
		super(source, null, null, type);
		this.constantValue = constantValue;
	}

	@Override
	public String toString() {
		return "$proc_null";
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.PROC_NULL;
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
		return true;
	}

}
