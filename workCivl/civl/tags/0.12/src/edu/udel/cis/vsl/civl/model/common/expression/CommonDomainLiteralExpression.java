package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.DomainLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public class CommonDomainLiteralExpression extends CommonExpression implements
		DomainLiteralExpression {

	private Expression[] ranges;

	public CommonDomainLiteralExpression(CIVLSource source,
			List<Expression> ranges, CIVLType type) {
		super(source);
		this.ranges = new Expression[ranges.size()];
		ranges.toArray(this.ranges);
		this.expressionType = type;
	}

	@Override
	public LiteralKind literalKind() {
		return LiteralKind.DOMAIN;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.DOMAIN_LITERAL;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		Set<Variable> result = new HashSet<>();

		if (this.ranges != null) {
			for (Expression range : ranges) {
				Set<Variable> rangeResult = range.variableAddressedOf(scope);

				if (rangeResult != null)
					result.addAll(rangeResult);
			}
		}
		return result;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		Set<Variable> result = new HashSet<>();

		if (this.ranges != null) {
			for (Expression range : ranges) {
				Set<Variable> rangeResult = range.variableAddressedOf();

				if (rangeResult != null)
					result.addAll(rangeResult);
			}
		}
		return result;
	}

	@Override
	public Expression rangeAt(int index) {
		return ranges[index];
	}

	@Override
	public int dimension() {
		return ranges.length;
	}

	@Override
	public String toString() {
		StringBuffer string = new StringBuffer();
		int dim = this.dimension();
		boolean first = true;

		string.append("{");
		for (int i = 0; i < dim; i++) {
			if (first)
				first = false;
			else
				string.append(", ");
			string.append(ranges[i]);
		}
		string.append("}");
		return string.toString();
	}
}
