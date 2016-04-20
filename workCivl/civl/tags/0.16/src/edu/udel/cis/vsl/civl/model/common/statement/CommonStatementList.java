package edu.udel.cis.vsl.civl.model.common.statement;

import java.util.ArrayList;
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
import edu.udel.cis.vsl.civl.model.IF.statement.StatementList;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;

/**
 * A list of statements that are to be executed in one step of a transition.
 * This class is only used during the execution of an atomic block: when
 * multiple processes want to resume from some previously blocked locations,
 * each process creates a new transition that has two statements, which are an
 * additional atomic lock variable assignment ($ATOMIC_LOCK_VAR=$self) and the
 * statement as usual.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class CommonStatementList implements StatementList {

	/* *************************** Instance Fields ************************* */

	/**
	 * The list of statements to be executed sequentially within one step.
	 */
	private ArrayList<Statement> statements;

	/* **************************** Constructors *************************** */

	/**
	 * Create an empty statement list.
	 */
	public CommonStatementList() {
		statements = new ArrayList<>();
	}

	/**
	 * Create a new statement list using a given list of statements.
	 * 
	 * @param stmts
	 *            The list of statements to be used for the new StatementList
	 *            object.
	 */
	public CommonStatementList(ArrayList<Statement> stmts) {
		statements = stmts;
	}

	/**
	 * Create a new statement list using a given statement.
	 * 
	 * @param statement
	 *            The statement to be used to create the statement list.
	 */
	public CommonStatementList(Statement statement) {
		statements = new ArrayList<>();
		this.statements.add(statement);
	}

	/**
	 * Create a new statement list using a two given statements.
	 * 
	 * @param statement1
	 *            The first statement in the list.
	 * @param statement2
	 *            The second statement in the list.
	 */
	public CommonStatementList(Statement statement1, Statement statement2) {
		statements = new ArrayList<>(2);
		this.statements.add(statement1);
		this.statements.add(statement2);
	}

	/* *************************** Public Methods ************************ */

	/**
	 * Add a new statement to the list.
	 * 
	 * @param statement
	 *            The new statement to be added into the list.
	 */
	public void add(Statement statement) {
		this.statements.add(statement);
	}

	/**
	 * 
	 * @return The list of statements of this Statement List.
	 */
	public ArrayList<Statement> statements() {
		return this.statements;
	}

	/* ********************** Methods from Sourceable ********************** */

	/**
	 * {@inheritDoc} If the first statement is created by the executor rather
	 * than a "real" statement, then use the source of the second statement.
	 */
	@Override
	public CIVLSource getSource() {
		CIVLSource result = null;

		if (!statements.isEmpty()) {
			result = statements.get(0).getSource();

			if (result.isSystemSource()) {
				if (statements.size() > 1) {
					result = statements.get(1).getSource();
				}
			}
		}
		return result;
	}

	@Override
	public void calculateDerefs() {
	}

	@Override
	public Expression guard() {
		if (!statements.isEmpty()) {
			Statement first = statements.get(0);

			if (first.getSource().isSystemSource()) {
				if (statements.size() > 1) {
					return statements.get(1).guard();
				}
			}
			return first.guard();
		}
		return null;
	}

	@Override
	public boolean hasDerefs() {
		return false;
	}

	@Override
	public boolean isPurelyLocal() {
		return false;
	}

	@Override
	public Model model() {
		return null;
	}

	@Override
	public void purelyLocalAnalysis() {

	}

	@Override
	public void purelyLocalAnalysisOfVariables(Scope funcScope) {
	}

	@Override
	public Statement replaceWith(ConditionalExpression oldExpression,
			Expression newExpression) {
		return null;
	}

	@Override
	public void replaceWith(ConditionalExpression oldExpression,
			VariableExpression newExpression) {

	}

	@Override
	public void setGuard(Expression guard) {
	}

	@Override
	public void setModel(Model model) {
	}

	/* *********************** Methods from Statement ********************** */

	@Override
	public void setSource(Location source) {
	}

	@Override
	public void setTarget(Location target) {
	}

	@Override
	public Location source() {
		if (!statements.isEmpty()) {
			Statement first = statements.get(0);

			if (first.getSource().isSystemSource()) {
				if (statements.size() > 1) {
					return statements.get(1).source();
				}
			}
			return first.source();
		}
		return null;
	}

	@Override
	public Scope statementScope() {
		return null;
	}

	@Override
	public Location target() {
		if (!statements.isEmpty()) {
			return statements.get(statements.size() - 1).target();
		}
		return null;
	}

	/* ************************* Methods from Object *********************** */

	@Override
	public String toString() {
		String result = "";
		for (Statement s : statements) {

			if (s.getSource().isSystemSource())
				result = "(" + s.toString() + ") ";
			else
				result = result + s.toString() + "; ";
		}
		result = result.trim();
		result = result.substring(0, result.length() - 1);
		return result;
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
	public StatementKind statementKind() {
		return StatementKind.STATEMENT_LIST;
	}

	@Override
	public String toStepString(AtomicKind atomicKind, int atomCount,
			boolean atomicLockVarChanged) {
		String result = "  " + this.source().id() + "->";

		if (this.target() != null)
			result += this.target().id() + ": ";
		else
			result += "RET: ";
		switch (atomicKind) {
		case ATOMIC_ENTER:
			if (atomicLockVarChanged) {
				result += toString() + " ";
			} else
				result += "ENTER_ATOMIC (atomicCount++) ";
			result += Integer.toString(atomCount - 1);
			break;
		case ATOMIC_EXIT:
			if (atomicLockVarChanged) {
				result += toString() + " ";
			} else
				result += "LEAVE_ATOMIC (atomicCount--) ";
			result += Integer.toString(atomCount);
			break;
		case ATOM_ENTER:
			result += toString() + " ";
			result += Integer.toString(atomCount - 1);
			break;
		case ATOM_EXIT:
			result += toString() + " ";
			result += Integer.toString(atomCount);
			break;
		default:
			result += toString();
		}
		if (this.getSource() != null)
			result += " at " + getSource().getSummary();
		else
			result += " at " + this.source().getSource().getSummary();
		result += ";";
		return result;
	}

	@Override
	public void setTargetTemp(Location target) {
	}

	@Override
	public void calculateConstantValue(SymbolicUniverse universe) {
	}

}
