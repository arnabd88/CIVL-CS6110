package edu.udel.cis.vsl.civl.model.common.statement;

import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.CivlForEnterStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;

public class CommonCivlForEnterStatement extends CommonStatement implements
		CivlForEnterStatement {

	private Expression domain;

	private List<Variable> loopVariables;

	private Variable literalDomCounter;

	public CommonCivlForEnterStatement(CIVLSource civlSource, Location source,
			Expression guard, Expression dom, List<Variable> variables,
			Variable counter) {
		super(civlSource, dom.expressionScope(), dom.lowestScope(), source,
				guard);
		this.domain = dom;
		this.setLoopVariables(variables);
		this.literalDomCounter = counter;
	}

	@Override
	public Statement replaceWith(ConditionalExpression oldExpression,
			Expression newExpression) {
		Expression newGuard = guardReplaceWith(oldExpression, newExpression);
		CivlForEnterStatement newStatement = null;

		if (newGuard != null) {
			newStatement = new CommonCivlForEnterStatement(this.getSource(),
					this.source(), newGuard, this.domain, this.loopVariables,
					this.literalDomCounter);
		} else {
			Expression newDomain = domain.replaceWith(oldExpression,
					newExpression);

			if (newDomain != null) {
				newStatement = new CommonCivlForEnterStatement(
						this.getSource(), this.source(), this.guard(),
						newDomain, this.loopVariables, this.literalDomCounter);
			}
		}
		return newStatement;
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
	public StatementKind statementKind() {
		return StatementKind.CIVL_FOR_ENTER;
	}

	@Override
	public Expression domain() {
		return this.domain;
	}

	@Override
	public List<Variable> loopVariables() {
		return this.loopVariables;
	}

	public void setLoopVariables(List<Variable> loopVariables) {
		this.loopVariables = loopVariables;
	}

	@Override
	public String toString() {
		StringBuffer string = new StringBuffer();
		int dim = this.loopVariables.size();
		boolean first = true;

		string.append("NEXT ");
		string.append("(");
		for (int i = 0; i < dim; i++) {
			if (first)
				first = false;
			else
				string.append(", ");
			string.append(this.loopVariables.get(i));
		}
		string.append(") in ");
		string.append(domain);
		return string.toString();
	}

	@Override
	public Variable getLiteralDomCounter() {
		return this.literalDomCounter;
	}

	@Override
	protected void calculateConstantValueWork(SymbolicUniverse universe) {
		this.domain.calculateConstantValue(universe);
	}
}
