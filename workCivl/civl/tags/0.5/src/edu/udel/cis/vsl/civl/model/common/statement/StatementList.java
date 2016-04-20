package edu.udel.cis.vsl.civl.model.common.statement;

import java.util.ArrayList;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;

/**
 * A list of statements that are to be executed in one transition. This class is
 * only used during the execution of an atomic block: when multiple processes
 * want to resume from some previously blocked locations, each process creates a
 * new transition that has two statements, which are an additional atomic lock
 * variable assignment ($ATOMIC_LOCK_VAR=$self) and the statement as usual.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class StatementList implements Statement {
	/**
	 * The list of statements to be executed sequentially
	 */
	private ArrayList<Statement> statements;

	public StatementList() {
		statements = new ArrayList<Statement>();
	}

	public StatementList(ArrayList<Statement> stmts) {
		statements = stmts;
	}

	public StatementList(Statement statement) {
		statements = new ArrayList<Statement>();
		this.statements.add(statement);
	}

	public ArrayList<Statement> statements() {
		return this.statements;
	}

	public void add(Statement statement) {
		this.statements.add(statement);
	}

	/**
	 * {@inheritDoc} If the first statement is created by the executor rather
	 * than a "real" statement, then use the source of the second statement.
	 */
	@Override
	public CIVLSource getSource() {
		CIVLSource result = null;

		if (!statements.isEmpty()) {
			result = statements.get(0).getSource();
			if (result.getLocation() == "CIVL System object") {
				if (statements.size() > 1) {
					result = statements.get(1).getSource();
				}
			}
		}
		return result;
	}

	@Override
	public Location source() {
		if (!statements.isEmpty()) {
			Statement first = statements.get(0);

			if (first.getSource().getLocation() == "CIVL System object") {
				if (statements.size() > 1) {
					return statements.get(1).source();
				}
			}
			return first.source();
		}
		return null;
	}

	@Override
	public Location target() {
		if (!statements.isEmpty()) {
			return statements.get(statements.size() - 1).target();
		}
		return null;
	}

	@Override
	public Expression guard() {
		if (!statements.isEmpty()) {
			Statement first = statements.get(0);

			if (first.getSource().getLocation() == "CIVL System object") {
				if (statements.size() > 1) {
					return statements.get(1).guard();
				}
			}
			return first.guard();
		}
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
		return false;
	}

	@Override
	public void calculateDerefs() {
	}

	@Override
	public void purelyLocalAnalysisOfVariables(Scope funcScope) {
	}

	@Override
	public boolean isPurelyLocal() {
		return false;
	}

	@Override
	public void purelyLocalAnalysis() {

	}

	@Override
	public void replaceWith(ConditionalExpression oldExpression,
			VariableExpression newExpression) {

	}

	@Override
	public Statement replaceWith(ConditionalExpression oldExpression,
			Expression newExpression) {
		return null;
	}

	@Override
	public String toString() {
		String result = "";
		for (Statement s : statements) {
			result = result + s.toString() + "; ";
		}
		
		return result.trim();
	}
}
