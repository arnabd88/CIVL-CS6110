/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.statement;

import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.Sourceable;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;

/**
 * The parent of all statements.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface Statement extends Sourceable {

	/**
	 * @return The location that is the source of this statement.
	 */
	Location source();

	/**
	 * @return The location that is the target of this statement.
	 */
	Location target();

	/**
	 * @return The boolean-valued guard expression for this statement.
	 */
	Expression guard();

	/**
	 * @return The model to which this statement belongs.
	 */
	Model model();

	/**
	 * @param source
	 *            the source to set
	 */
	void setSource(Location source);

	/**
	 * @param target
	 *            the target to set
	 */
	void setTarget(Location target);

	/**
	 * @param guard
	 *            the guard to set
	 */
	void setGuard(Expression guard);

	/**
	 * @param model
	 *            The Model to which this statement belongs.
	 */
	void setModel(Model model);

	/**
	 * @return The highest scope accessed by this statement. Null if no
	 *         variables accessed.
	 */
	Scope statementScope();

	/**
	 * @param statementScope
	 *            The highest scope accessed by this statement. Null if no
	 *            variables accessed.
	 */
	void setStatementScope(Scope statementScope);

	/**
	 * return true iff the statement has at least one dereferences
	 * 
	 * @return True of False
	 */
	boolean hasDerefs();

	/**
	 * Calculate if this statement contains any dereference expression
	 */
	void calculateDerefs();

	/**
	 * if an &(var) is encountered, then var is considered as no purely local if
	 * a statement inside a function with fscope is accessing some variable that
	 * is declared in the scope vscope such that fscope.isDescendantOf(vscope),
	 * then that variable is not purely local
	 * 
	 * @param funcScope
	 *            the function scope of the statement
	 */
	void purelyLocalAnalysisOfVariables(Scope funcScope);

	/**
	 * @return True iff the statement accesses only purely-local variables
	 */
	boolean isPurelyLocal();

	/**
	 * Analyze if this statement accesses any non-purely-local variables
	 */
	void purelyLocalAnalysis();

	/**
	 * Modify this statement by replacing a certain conditional expression with
	 * a variable expression, used when translating away conditional expression
	 * and a temporal variable is introduced.
	 * 
	 * @param oldExpression
	 *            The conditional expression
	 * @param newExpression
	 *            The variable expression of the temporal variable for the
	 *            conditional expression
	 */
	void replaceWith(ConditionalExpression oldExpression,
			VariableExpression newExpression);

	/**
	 * Return a new statement by replacing this statement by replacing a certain
	 * conditional expression with a expression, used when translating away
	 * conditional expression without introducing temporal variables.
	 * 
	 * @param oldExpression
	 *            The conditional expression
	 * @param newExpression
	 *            The new expression
	 * @return A new statement without the conditional expression
	 */
	Statement replaceWith(ConditionalExpression oldExpression,
			Expression newExpression);

}
