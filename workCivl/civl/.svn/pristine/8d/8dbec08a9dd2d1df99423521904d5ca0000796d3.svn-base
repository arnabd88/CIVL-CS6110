/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.statement;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.Sourceable;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.location.Location.AtomicKind;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;

/**
 * The parent of all statements.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface Statement extends Sourceable {

	/* ********************************* Types ***************************** */

	/**
	 * Different kinds of statements.
	 * 
	 * @author Manchun Zheng (zmanchun)
	 * 
	 */
	public enum StatementKind {
		ASSERT, /** Assertion */
		ASSIGN, /** Assignment */
		ASSUME, /** Assumption */
		CALL_OR_SPAWN, /** Function call or process spawn */
		// CHOOSE, /** Non-deterministic choice */
		CIVL_FOR_ENTER, /** CIVL for loop ($for) enter statement */
		CIVL_PAR_FOR_ENTER, /** CIVL parallel for ($par) enter statement */
		MALLOC, /** Memory allocation */
		NOOP, /** No operation */
		STATEMENT_SET, /** Non-malicious statement, e.g., statement set */
		// TODO get rid of this
		RETURN, /** Return statement */
		STATEMENT_LIST,
		/** Statement list */
	}

	/* **************************** Public Methods ************************* */

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
	 * @param target
	 *            the target to set
	 */
	void setTargetTemp(Location target);

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
	 * Modify this statement including its guard by replacing a certain
	 * conditional expression with a variable expression, used when translating
	 * away conditional expression and a temporal variable is introduced.<br>
	 * For example, <code>x = a ? b : c</code> will be translated into
	 * <code> if(a) v0 = b; else v0 = c; x = v0; </code><br>
	 * Another example, <code> $when(a?b:c) x = k;</code> will be translated
	 * into <code> if(a) v0 = b; else v0 = c; $when(v0) x = k; </code>
	 * 
	 * @param oldExpression
	 *            The conditional expression to be cleared.
	 * @param newExpression
	 *            The variable expression of the temporal variable for the
	 *            conditional expression.
	 */
	void replaceWith(ConditionalExpression oldExpression,
			VariableExpression newExpression);

	/**
	 * Return a new statement by copying this statement and modifying it as well
	 * as its guard by replacing a certain conditional expression with a
	 * expression, used when translating away conditional expression WITHOUT
	 * introducing temporary variables. The original statement can't be
	 * modified, because it needs to be used twice to generate the if branch
	 * statement and the else branch statement.<br>
	 * For example, <code>x = a ? b : c</code> will be translated into
	 * <code> if(a) x = b; else x = c; </code><br>
	 * Another example, <code> $when(a?b:c) x = k;</code> will be translated
	 * into <code> if(a) $when(b) x=k; else $when(c) x=k; </code>
	 * 
	 * @param oldExpression
	 *            The conditional expression to be cleared.
	 * @param newExpression
	 *            The new expression to take place of the conditional
	 *            expression. Usually, it is one of the choice expressions of
	 *            the conditional expression.
	 * @return A new statement without the conditional expression
	 */
	Statement replaceWith(ConditionalExpression oldExpression,
			Expression newExpression);

	/**
	 * Obtain the set of variables visible from a certain scope that are
	 * possible to be written in the future.
	 * 
	 * @param scope
	 *            The given scope.
	 * @return
	 */
	Set<Variable> variableAddressedOf(Scope scope);

	/**
	 * Obtain the set of variables whose addresses are referenced.
	 * 
	 * @return
	 */
	Set<Variable> variableAddressedOf();

	/**
	 * Obtain the kind of the statement.
	 * 
	 * @return The statement's kind.
	 */
	StatementKind statementKind();

	String toStepString(AtomicKind atomicKind, int atomCount,
			boolean atomicLockVarChanged);

	/**
	 * Obtains the lowest scope of expression accessed by this statement.
	 * 
	 * @return the lowest scope of expression accessed by this statement.
	 */
	Scope lowestScope();

	void calculateConstantValue(SymbolicUniverse universe);
}
