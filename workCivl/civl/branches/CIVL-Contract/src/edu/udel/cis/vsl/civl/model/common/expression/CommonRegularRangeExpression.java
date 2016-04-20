package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.RegularRangeExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;

public class CommonRegularRangeExpression extends CommonExpression implements
		RegularRangeExpression {

	private Expression low;
	private Expression high;
	private Expression step;

	public CommonRegularRangeExpression(CIVLSource source, Scope hscope,
			Scope lscope, CIVLType type, Expression low, Expression high,
			Expression step) {
		super(source, hscope, lscope, type);
		this.low = low;
		this.high = high;
		this.step = step;
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

	@Override
	public void calculateConstantValueWork(SymbolicUniverse universe) {
		SymbolicExpression lowValue, highValue, stepValue;
		BooleanExpression claim;
		ResultType validity;
		boolean negativeStep = false;

		low.calculateConstantValue(universe);
		high.calculateConstantValue(universe);
		step.calculateConstantValue(universe);
		lowValue = low.constantValue();
		highValue = high.constantValue();
		stepValue = step.constantValue();
		if (lowValue == null || highValue == null || stepValue == null)
			return;
		claim = universe.equals(universe.zeroInt(), stepValue);
		validity = universe.reasoner(universe.trueExpression()).valid(claim)
				.getResultType();
		if (validity == ResultType.YES)
			return;
		claim = universe.lessThan(universe.zeroInt(), (NumericExpression) stepValue);
		validity = universe.reasoner(universe.trueExpression()).valid(claim)
				.getResultType();
		if (validity == ResultType.NO)
			negativeStep = true;
		if (negativeStep) {
			SymbolicExpression tmp = lowValue;

			lowValue = highValue;
			highValue = tmp;
		}
		constantValue = universe.tuple((SymbolicTupleType) this.expressionType
				.getDynamicType(universe), Arrays.asList(lowValue, highValue,
				stepValue));
	}

	@Override
	protected boolean expressionEquals(Expression expression) {
		RegularRangeExpression that = (RegularRangeExpression) expression;

		return this.low.equals(that.getLow())
				&& this.high.equals(that.getHigh())
				&& this.step.equals(that.getStep());
	}

}
