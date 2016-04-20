package edu.udel.cis.vsl.civl.model.common.statement;

import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.CivlForEnterStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public class CommonCivlForEnterStatement extends CommonStatement implements
		CivlForEnterStatement {

	private Expression domain;

	private List<VariableExpression> loopVariables;

	public CommonCivlForEnterStatement(CIVLSource civlSource, Location source,
			Expression dom, List<VariableExpression> variables) {
		super(civlSource, source);
		this.domain = dom;
		this.setLoopVariables(variables);
	}

	@Override
	public Statement replaceWith(ConditionalExpression oldExpression,
			Expression newExpression) {
		Expression newGuard = guardReplaceWith(oldExpression, newExpression);
		CivlForEnterStatement newStatement = null;

		if (newGuard != null) {
			newStatement = new CommonCivlForEnterStatement(this.getSource(),
					this.source(), this.domain, this.loopVariables);
			newStatement.setGuard(newGuard);
		} else {
			Expression newDomain = domain.replaceWith(oldExpression,
					newExpression);

			if (newDomain != null) {
				newStatement = new CommonCivlForEnterStatement(
						this.getSource(), this.source(), newDomain,
						this.loopVariables);
				newStatement.setGuard(this.guard());
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
	public List<VariableExpression> loopVariables() {
		return this.loopVariables;
	}

	public void setLoopVariables(List<VariableExpression> loopVariables) {
		this.loopVariables = loopVariables;
	}

	@Override
	public String toString() {
		StringBuffer string = new StringBuffer();
		int dim = this.loopVariables.size();
		boolean first = true;

		string.append("CIVL_FOR_ENTER: ");
		string.append("(");
		for (int i = 0; i < dim; i++) {
			if (first)
				first = false;
			else
				string.append(", ");
			string.append(this.loopVariables.get(i));
		}
		string.append(") : ");
		string.append(domain);
		return string.toString();
	}
}
