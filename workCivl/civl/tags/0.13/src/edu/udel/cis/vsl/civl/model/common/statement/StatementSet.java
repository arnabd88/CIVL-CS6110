package edu.udel.cis.vsl.civl.model.common.statement;

import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.location.Location.AtomicKind;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * Sometimes it is useful for the model builder to return a set of statements.
 * e.g. when exiting a switch the end of the default case and all break
 * statements need their targets set to the source location of the next
 * statement.
 * 
 * @author zirkel
 * 
 */
public class StatementSet implements Statement {

	private Set<Statement> statements;
	private boolean hasDerefs;
	private boolean purelyLocal;

	public StatementSet() {
		statements = new LinkedHashSet<Statement>();
	}

	public StatementSet(Set<Statement> statements) {
		this.statements = statements;
	}

	public Set<Statement> statements() {
		return statements;
	}

	public void add(Statement statement) {
		statements.add(statement);
	}

	@Override
	public CIVLSource getSource() {
		return null;
	}

	@Override
	public Location source() {
		return null;
	}

	@Override
	public Location target() {
		return null;
	}

	@Override
	public Expression guard() {
		return null;
	}

	@Override
	public Model model() {
		return null;
	}

	@Override
	public void setSource(Location source) {

	}

	@Override
	public void setTarget(Location target) {
		for (Statement s : statements) {
			s.setTarget(target);
		}
	}

	@Override
	public void setGuard(Expression guard) {

	}

	@Override
	public void setModel(Model model) {

	}

	@Override
	public Scope statementScope() {
		return null;
	}

	@Override
	public void setStatementScope(Scope statementScope) {

	}

	@Override
	public boolean hasDerefs() {
		return this.hasDerefs;
	}

	@Override
	public void calculateDerefs() {
		this.hasDerefs = false;
		for (Statement s : statements) {
			s.calculateDerefs();
			this.hasDerefs = this.hasDerefs || s.hasDerefs();
			// early return
			if (this.hasDerefs)
				return;
		}
	}

	@Override
	public boolean isPurelyLocal() {
		return this.purelyLocal;
	}

	@Override
	public void purelyLocalAnalysisOfVariables(Scope funcScope) {
		for (Statement s : statements) {
			s.purelyLocalAnalysisOfVariables(funcScope);
		}
	}

	@Override
	public void purelyLocalAnalysis() {
		this.guard().purelyLocalAnalysis();
		if (!this.guard().isPurelyLocal()) {
			this.purelyLocal = false;
			return;
		}

		for (Statement s : statements) {
			s.purelyLocalAnalysis();
			if (!s.isPurelyLocal()) {
				this.purelyLocal = false;
				return;
			}
		}
		this.purelyLocal = true;
	}

	@Override
	public void replaceWith(ConditionalExpression oldExpression,
			VariableExpression newExpression) {
		for (Statement s : this.statements) {
			s.replaceWith(oldExpression, newExpression);
		}
	}

	@Override
	public Statement replaceWith(ConditionalExpression oldExpression,
			Expression newExpression) {
		boolean hasNewStatement = false;
		Set<Statement> newStatements = new HashSet<Statement>();
		StatementSet result = null;

		for (Statement s : this.statements) {
			if (hasNewStatement)
				newStatements.add(s);
			else {
				Statement newStatement = s.replaceWith(oldExpression,
						newExpression);

				if (newStatement != null) {
					newStatements.add(newStatement);
					hasNewStatement = true;
				} else
					newStatements.add(s);
			}
		}

		if (hasNewStatement) {
			result = new StatementSet(newStatements);
		}

		return result;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public StatementKind statementKind() {
		return StatementKind.OTHERS;
	}

	@Override
	public String toStepString(AtomicKind atomicKind, int atomCount,
			boolean atomicLockVarChanged) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void setTargetTemp(Location target) {
		// TODO Auto-generated method stub

	}

}
