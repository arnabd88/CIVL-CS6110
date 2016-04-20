/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.statement;

import java.util.Vector;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.common.CommonSourceable;
import edu.udel.cis.vsl.civl.model.common.expression.CommonBooleanLiteralExpression;

/**
 * The parent of all statements.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonStatement extends CommonSourceable implements Statement {

	private Location source;
	private Location target;
	private Expression guard;
	private Model model;
	protected Scope statementScope = null;

	/**
	 * The parent of all statements.
	 * 
	 * @param source
	 *            The location that is the source of this statement.
	 */
	public CommonStatement(CIVLSource civlSource, Location source) {
		super(civlSource);
		this.source = source;
		guard = new CommonBooleanLiteralExpression(civlSource, true);
		source.addOutgoing(this);
	}

	/**
	 * @return The location that is the source of this statement.
	 */
	@Override
	public Location source() {
		return source;
	}

	/**
	 * @return The location that is the target of this statement.
	 */
	@Override
	public Location target() {
		return target;
	}

	/**
	 * @return The boolean-valued guard expression for this statement.
	 */
	@Override
	public Expression guard() {
		return guard;
	}
	
	/**
	 * @return The model to which this statement belongs.
	 */
	@Override
	public Model model() {
		return model;
	}

	/**
	 * @param source
	 *            the source to set
	 */
	@Override
	public void setSource(Location source) {
		if (this.source != null) {
			this.source.outgoing().remove(this);
		}
		this.source = source;
		source.addOutgoing(this);
	}

	/**
	 * @param target
	 *            the target to set
	 */
	@Override
	public void setTarget(Location target) {
		if (this.target != null) {
			this.target().incoming().remove(this);
		}
		this.target = target;
		target.addIncoming(this);
	}

	/**
	 * @param guard
	 *            the guard to set
	 */
	@Override
	public void setGuard(Expression guard) {
		this.guard = guard;
		statementScope = join(statementScope, guard.expressionScope());
	}

	/**
	 * @param model The Model to which this statement belongs.
	 */
	@Override
	public void setModel(Model model) {
		this.model = model;
	}
	
	
	/**
	 * @return The highest scope accessed by this statement. Null if no
	 *         variables accessed.
	 */
	@Override
	public Scope statementScope() {
		return statementScope;
	}

	/**
	 * @param statementScope
	 *            The highest scope accessed by this statement. Null if no
	 *            variables accessed.
	 */
	@Override
	public void setStatementScope(Scope statementScope) {
		this.statementScope = statementScope;
	}

	/**
	 * @param s0
	 *            A scope. May be null.
	 * @param s1
	 *            A scope. May be null.
	 * @return The scope that is the join, or least common ancestor in the scope
	 *         tree, of s0 and s1. Null if both are null. If exactly one of s0
	 *         and s1 are null, returns the non-null scope.
	 */
	protected Scope join(Scope s0, Scope s1) {
		Vector<Scope> s0Ancestors = new Vector<Scope>();
		Scope s0Ancestor = s0;
		Scope s1Ancestor = s1;

		if (s0 == null) {
			return s1;
		} else if (s1 == null) {
			return s0;
		}
		s0Ancestors.add(s0Ancestor);
		while (s0Ancestor.parent() != null) {
			s0Ancestor = s0Ancestor.parent();
			s0Ancestors.add(s0Ancestor);
		}
		while (true) {
			if (s0Ancestors.contains(s1Ancestor)) {
				return s1Ancestor;
			}
			s1Ancestor = s1Ancestor.parent();
		}
	}

}
