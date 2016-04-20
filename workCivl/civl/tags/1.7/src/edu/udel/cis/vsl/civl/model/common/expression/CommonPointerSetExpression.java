package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.PointerSetExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public class CommonPointerSetExpression extends CommonExpression implements
		PointerSetExpression {
	private LHSExpression basePointer;

	private Expression range;

	public CommonPointerSetExpression(CIVLSource source, Scope hscope,
			Scope lscope, CIVLType type, LHSExpression basePointer,
			Expression range) {
		super(source, hscope, lscope, type);
		this.basePointer = basePointer;
		this.range = range;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.POINTER_SET;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		Set<Variable> result = basePointer.variableAddressedOf(scope);

		result.addAll(range.variableAddressedOf(scope));
		return result;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		Set<Variable> result = basePointer.variableAddressedOf();

		result.addAll(range.variableAddressedOf());
		return result;
	}

	@Override
	public LHSExpression getBasePointer() {
		return basePointer;
	}

	@Override
	public Expression getRange() {
		return range;
	}

	@Override
	protected boolean expressionEquals(Expression expression) {
		if (expression instanceof PointerSetExpression) {
			PointerSetExpression mem = (PointerSetExpression) expression;

			if (mem.getBasePointer().equals(basePointer))
				if (mem.getRange().equals(range))
					return true;
		}

		return false;
	}

	@Override
	public String toString() {
		if (range != null)
			return "{" + this.basePointer + " + " + this.range + "}";
		else
			return "{" + this.basePointer + "}";
	}
}
