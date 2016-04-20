package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.DomainGuardExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLCompleteDomainType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public class CommonDomainGuardExpression extends CommonExpression implements
		DomainGuardExpression {

	private Variable[] variables;

	private Expression domain;

	private Variable literalDomCounter;

	public CommonDomainGuardExpression(CIVLSource source, CIVLType type,
			Expression dom, List<Variable> vars, Variable counter) {
		super(source, dom.expressionScope(), dom.expressionScope(), type);
		this.variables = new Variable[vars.size()];
		vars.toArray(this.variables);
		this.domain = dom;
		this.literalDomCounter = counter;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.DOMAIN_GUARD;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		return null;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		return null;
	}

	@Override
	public Expression domain() {
		return this.domain;
	}

	@Override
	public int dimension() {
		// Since this is in a domain for loop so it's guaranteed to be a
		// complete domain type. That's why this cast is safe.
		return ((CIVLCompleteDomainType) this.domain.getExpressionType())
				.getDimension();
	}

	@Override
	public Variable variableAt(int index) {
		return this.variables[index];
	}

	@Override
	public String toString() {
		StringBuffer string = new StringBuffer();
		int dim = this.dimension();
		boolean first = true;

		string.append(domain);
		string.append(" has next for (");
		for (int i = 0; i < dim; i++) {
			if (first)
				first = false;
			else
				string.append(", ");
			string.append(variables[i].name().name());
		}
		string.append(")");
		return string.toString();
	}

	@Override
	public Variable getLiteralDomCounter() {
		return this.literalDomCounter;
	}

	@Override
	protected boolean expressionEquals(Expression expression) {
		return this.domain
				.equals(((DomainGuardExpression) expression).domain());
	}
}
