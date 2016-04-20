package edu.udel.cis.vsl.civl.model.IF.expression;

import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * A left-hand-side expression. This can be used on the left hand side of an
 * assignment, or as the argument to address-of (&).
 * 
 * Variable expressions, subscript expressions, dereference expressions, and dot
 * expressions are all LHS expressions.
 * 
 * @author siegel
 * 
 */
public interface LHSExpression extends Expression {

	public enum LHSExpressionKind {
		DEREFERENCE, DOT, SUBSCRIPT, VARIABLE
	}

	LHSExpressionKind lhsExpressionKind();

	/**
	 * Updates the flag of the expression denoting if it is purely local.
	 * 
	 * @param pl
	 *            True iff attempting to set the expression as purely local.
	 */
	void setPurelyLocal(boolean pl);

	/**
	 * Return the variable that is visible from the given scope, which is
	 * possible the left hand side of an assignment statement.
	 * 
	 * @param scope
	 *            The given scope.
	 * @return
	 */
	Variable variableWritten(Scope scope);

	/**
	 * Return the variable that is possible the left hand side of an assignment
	 * statement.
	 * 
	 * @param scope
	 *            The given scope.
	 * @return
	 */
	Variable variableWritten();
}
