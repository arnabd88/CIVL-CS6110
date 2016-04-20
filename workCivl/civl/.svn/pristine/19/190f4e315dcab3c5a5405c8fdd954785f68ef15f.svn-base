package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.DomainInitializer;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLDomainType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public class CommonDomainInitializer extends CommonExpression implements
		DomainInitializer {

	private int index;
	private Expression domain;
	private boolean isLast;

	public CommonDomainInitializer(CIVLSource source, CIVLType type, int index,
			Expression dom, boolean isLast) {
		super(source);
		this.expressionType = type;
		this.index = index;
		this.domain = dom;
		this.isLast = isLast;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.DOMAIN_INIT;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		return domain.variableAddressedOf(scope);
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		return domain.variableAddressedOf();
	}

	@Override
	public int index() {
		return this.index;
	}

	@Override
	public Expression domain() {
		return this.domain;
	}

	@Override
	public int dimension() {
		return ((CIVLDomainType) domain.getExpressionType()).dimension();
	}

	@Override
	public String toString() {
		StringBuffer string = new StringBuffer();

		string.append("domainInit(");
		string.append(domain);
		string.append(", ");
		string.append(index);
		string.append(")");
		return string.toString();
	}

	@Override
	public boolean isLast() {
		return this.isLast;
	}
}
