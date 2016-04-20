package edu.udel.cis.vsl.civl.model.common.expression;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.SizeofExpressionExpression;

public class CommonSizeofExpressionExpression extends CommonExpression
		implements SizeofExpressionExpression {

	private Expression argument;

	public CommonSizeofExpressionExpression(CIVLSource source,
			Expression argument) {
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
		if(this.hasDerefs){
			this.purelyLocal = false;
			return;
		}
		
		this.argument.purelyLocalAnalysis();
		this.purelyLocal = this.argument.isPurelyLocal();
	}
}
