package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.HashSet;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.AddressOfExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public class CommonAddressOfExpression extends CommonExpression implements
		AddressOfExpression {

	private LHSExpression operand;

	/**
	 * Constructor
	 * 
	 * @param source
	 *            The CIVL source
	 * @param operand
	 *            The operand
	 */
	public CommonAddressOfExpression(CIVLSource source, LHSExpression operand) {
		super(source);
		this.operand = operand;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.ADDRESS_OF;
	}

	@Override
	public LHSExpression operand() {
		return operand;
	}

	@Override
	public String toString() {
		return "&" + operand;
	}

	@Override
	public void calculateDerefs() {
		this.operand.calculateDerefs();
		this.hasDerefs = this.operand.hasDerefs();
	}

	@Override
	public void purelyLocalAnalysisOfVariables(Scope funcScope) {
		this.operand.setPurelyLocal(false);
	}

	@Override
	public void purelyLocalAnalysis() {
		if (this.hasDerefs) {
			this.purelyLocal = false;
			return;
		}
		this.operand.purelyLocalAnalysis();
		this.purelyLocal = this.operand.isPurelyLocal();
	}

	@Override
	public void replaceWith(ConditionalExpression oldExpression,
			VariableExpression newExpression) {
		if (operand == oldExpression) {
			operand = newExpression;
			return;
		}
		operand.replaceWith(oldExpression, newExpression);
	}

	@Override
	public Expression replaceWith(ConditionalExpression oldExpression,
			Expression newExpression) {
		Expression newOperand = operand.replaceWith(oldExpression,
				newExpression);
		CommonAddressOfExpression result = null;

		if (newOperand != null) {
			result = new CommonAddressOfExpression(this.getSource(),
					(LHSExpression) newOperand);
		}

		if (result != null)
			result.setExpressionType(expressionType);

		return result;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		Set<Variable> variableSet = new HashSet<>();
		Variable variableWritten = operand.variableWritten(scope);

		if (variableWritten != null)
			variableSet.add(variableWritten);
		return variableSet;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		Set<Variable> variableSet = new HashSet<>();
		Variable variableWritten = operand.variableWritten();

		if (variableWritten != null)
			variableSet.add(variableWritten);
		return variableSet;
	}

}
