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
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;

/**
 * A noop statement.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonNoopStatement extends CommonStatement implements
		NoopStatement {

	protected NoopKind noopKind;

	protected Expression expression;

	/**
	 * true iff this is a temporary noop inserted by the model translator
	 */
	private boolean isTemporary = false;

	private boolean removable = false;

	/**
	 * true iff this associates to a variable declaration
	 */
	private boolean isVariableDeclaration = false;

	/**
	 * A noop statement.
	 * 
	 * @param source
	 *            The source location for this noop.
	 */
	public CommonNoopStatement(CIVLSource civlSource, Location source,
			Expression guard, Expression expression) {
		super(civlSource, null, null, source, guard);
		noopKind = NoopKind.NONE;
		this.expression = expression;
	}

	/**
	 * A noop statement.
	 * 
	 * @param source
	 *            The source location for this noop.
	 */
	public CommonNoopStatement(CIVLSource civlSource, Location source,
			Expression guard, boolean isTemporary) {
		super(civlSource, null, null, source, guard);
		noopKind = NoopKind.NONE;
		this.isTemporary = isTemporary;
	}

	/**
	 * A noop statement.
	 * 
	 * @param source
	 *            The source location for this noop.
	 */
	public CommonNoopStatement(CIVLSource civlSource, Location source,
			Expression guard, boolean isTemporary, boolean isVariableDeclaration) {
		super(civlSource, null, null, source, guard);
		noopKind = NoopKind.NONE;
		this.isTemporary = isTemporary;
		this.isVariableDeclaration = isVariableDeclaration;
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
					this.source(), newGuard, expression);

		}
		Expression newExpressionArg = expression.replaceWith(oldExpression,
				newExpression);

		if (newExpressionArg != null)
			newStatement = new CommonNoopStatement(this.getSource(),
					this.source(), this.guard(), newExpressionArg);
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

	@Override
	protected void calculateConstantValueWork(SymbolicUniverse universe) {
	}

	@Override
	public Expression expression() {
		return this.expression;
	}

	@Override
	public void setRemovable() {
		removable = true;
	}

	@Override
	public boolean isRemovable() {
		return removable;
	}

	@Override
	public boolean isTemporary() {
		return this.isTemporary;
	}

	@Override
	public boolean isVariableDeclaration() {
		return this.isVariableDeclaration;
	}
}
