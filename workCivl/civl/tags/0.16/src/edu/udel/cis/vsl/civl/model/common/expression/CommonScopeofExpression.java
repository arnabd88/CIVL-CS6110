package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ScopeofExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * A scopeof expression is "$scopeof(expr)".
 * 
 * @author Manchun Zheng
 * 
 */
public class CommonScopeofExpression extends CommonExpression implements
		ScopeofExpression {

	private LHSExpression argument;

	public CommonScopeofExpression(CIVLSource source, CIVLType type,
			LHSExpression expression) {
		super(source, expression.expressionScope(), type);
		this.argument = expression;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.SCOPEOF;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		return argument.variableAddressedOf(scope);
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		return argument.variableAddressedOf();
	}

	@Override
	public LHSExpression argument() {
		return argument;
	}

	@Override
	public String toString() {
		return "$scopeof(" + argument + ")";
	}

}
