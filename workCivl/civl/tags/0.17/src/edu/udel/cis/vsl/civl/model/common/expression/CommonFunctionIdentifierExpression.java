package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.FunctionIdentifierExpression;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.model.common.type.CommonPointerType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class CommonFunctionIdentifierExpression extends CommonExpression
		implements FunctionIdentifierExpression {

	private CIVLFunction function;

	public CommonFunctionIdentifierExpression(CIVLSource source,
			CIVLFunction function, SymbolicType functionPointerType) {
		super(source, function.containingScope(), function.containingScope(),
				new CommonPointerType(function.functionType(),
						functionPointerType));
		this.function = function;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.FUNCTION_POINTER;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		return function.variableAddressedOf(scope);
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		return function.variableAddressedOf();
	}

	@Override
	public Scope scope() {
		return this.expressionScope();
	}

	@Override
	public CIVLFunction function() {
		return this.function;
	}

	@Override
	public String toString() {
		return function.name().name();
	}

	@Override
	protected boolean expressionEquals(Expression expression) {
		FunctionIdentifierExpression that = (FunctionIdentifierExpression) expression;

		return this.function.name().name()
				.equals(that.function().name().name());
	}
}
