/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.statement;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.NoopStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * A noop statement.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonNoopStatement extends CommonStatement implements
		NoopStatement {

	public enum NoopKind {
		IF_ELSE, SWITCH, LOOP, NONE, GOTO, ATOMIC_ATOM
	}

	protected NoopKind noopKind;

	/**
	 * A noop statement.
	 * 
	 * @param source
	 *            The source location for this noop.
	 */
	public CommonNoopStatement(CIVLSource civlSource, Location source) {
		super(civlSource, source);
		noopKind = NoopKind.NONE;
	}

	public CommonNoopStatement() {
		super();
	}

	@Override
	public String toString() {
		return "NO_OP";
	}

	@Override
	public Statement replaceWith(ConditionalExpression oldExpression,
			Expression newExpression) {
		Expression newGuard = guardReplaceWith(oldExpression, newExpression);
		CommonNoopStatement newStatement = null;

		if (newGuard != null) {
			newStatement = new CommonNoopStatement(this.getSource(),
					this.source());
			newStatement.setGuard(newGuard);
		}

		return newStatement;
	}

	@Override
	public NoopKind noopKind() {
		return this.noopKind;
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
		return StatementKind.NOOP;
	}

}
