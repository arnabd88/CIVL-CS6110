package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.FunctionPointerExpression;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.model.common.type.CommonPointerType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class CommonFunctionPointerExpression extends CommonExpression implements
		FunctionPointerExpression {

	private CIVLFunction function;

	public CommonFunctionPointerExpression(CIVLSource source,
			CIVLFunction function, SymbolicType pointerType) {
		super(source);
		this.function = function;
		this.expressionType = new CommonPointerType(function.functionType(),
				pointerType);
		this.setExpressionScope(function.containingScope());
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
}
