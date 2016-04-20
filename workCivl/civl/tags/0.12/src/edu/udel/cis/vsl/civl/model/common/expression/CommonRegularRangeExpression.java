package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.HashSet;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.RegularRangeExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public class CommonRegularRangeExpression extends CommonExpression implements
		RegularRangeExpression {

	private Expression low;
	private Expression high;
	private Expression step;

	public CommonRegularRangeExpression(CIVLSource source, CIVLType type,
			Expression low, Expression high, Expression step) {
		super(source);
		this.low = low;
		this.high = high;
		this.step = step;
		this.expressionType = type;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.REGULAR_RANGE;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		Set<Variable> variableSet = new HashSet<>();
		Set<Variable> operandResult = low.variableAddressedOf(scope);

		if (operandResult != null)
			variableSet.addAll(operandResult);
		operandResult = high.variableAddressedOf(scope);
		if (operandResult != null)
			variableSet.addAll(operandResult);
		operandResult = step.variableAddressedOf(scope);
		if (operandResult != null)
			variableSet.addAll(operandResult);
		return variableSet;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		Set<Variable> variableSet = new HashSet<>();
		Set<Variable> operandResult = low.variableAddressedOf();

		if (operandResult != null)
			variableSet.addAll(operandResult);
		operandResult = high.variableAddressedOf();
		if (operandResult != null)
			variableSet.addAll(operandResult);
		operandResult = step.variableAddressedOf();
		if (operandResult != null)
			variableSet.addAll(operandResult);
		return variableSet;
	}

	@Override
	public Expression getLow() {
		return this.low;
	}

	@Override
	public Expression getHigh() {
		return this.high;
	}

	@Override
	public Expression getStep() {
		return this.step;
	}
	
	@Override
	public String toString() {
		StringBuffer string = new StringBuffer();

		string.append(low);
		string.append("..");
		string.append(high);
		string.append("#");
		string.append(step);
		return string.toString();
	}

}
