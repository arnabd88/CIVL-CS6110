package edu.udel.cis.vsl.civl.model.common.expression;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.SizeofExpressionExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;

public class CommonSizeofExpression extends CommonExpression implements
		SizeofExpressionExpression {

	private Expression argument;

	public CommonSizeofExpression(CIVLSource source, Expression argument) {
		super(source);
		this.argument = argument;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.SIZEOF_EXPRESSION;
	}

	@Override
	public Expression getArgument() {
		return argument;
	}

	@Override
	public String toString() {
		return "sizeof(" + argument + ")";
	}

	@Override
	public void calculateDerefs() {
		this.argument.calculateDerefs();
		this.hasDerefs = this.argument.hasDerefs();
	}

	@Override
	public void purelyLocalAnalysisOfVariables(Scope funcScope) {
		this.argument.purelyLocalAnalysisOfVariables(funcScope);
	}

	@Override
	public void purelyLocalAnalysis() {
		if (this.hasDerefs) {
			this.purelyLocal = false;
			return;
		}

		this.argument.purelyLocalAnalysis();
		this.purelyLocal = this.argument.isPurelyLocal();
	}

	@Override
	public void replaceWith(ConditionalExpression oldExpression,
			VariableExpression newExpression) {
		if (argument == oldExpression) {
			argument = newExpression;
			return;
		}
		argument.replaceWith(oldExpression, newExpression);
	}

	@Override
	public Expression replaceWith(ConditionalExpression oldExpression,
			Expression newExpression) {
		Expression newArgument = argument.replaceWith(oldExpression,
				newExpression);
		CommonSizeofExpression result = null;

		if (newArgument != null) {
			result = new CommonSizeofExpression(this.getSource(), newArgument);
		}

		if (result != null)
			result.setExpressionType(expressionType);

		return result;
	}
}
