/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.expression;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.Sourceable;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * The parent of all expressions.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface Expression extends Sourceable {

	public enum ExpressionKind {
		/**
		 * A call to an abstract (mathematical) expression; instance of
		 * {@link AbstractFunctionCallExpression}.
		 */
		ABSTRACT_FUNCTION_CALL,
		/**
		 * A C address-of expression <code>&expr</code>, instance of
		 * {@link AddressOfExpression}.
		 */
		ADDRESS_OF, ARRAY_LITERAL, BINARY, BOOLEAN_LITERAL, BOUND_VARIABLE, CAST, CHAR_LITERAL, COND, DEREFERENCE, DERIVATIVE, DOMAIN_GUARD, DOT, DYNAMIC_TYPE_OF, FUNCTION_IDENTIFIER, FUNCTION_GUARD, INITIAL_VALUE, INTEGER_LITERAL, MEMORY_UNIT, MPI_CONTRACT_EXPRESSION, NULL_LITERAL, POINTER_SET, QUANTIFIER, REAL_LITERAL, REGULAR_RANGE, RESULT, SCOPEOF, SELF, SIZEOF_TYPE, SIZEOF_EXPRESSION, STRING_LITERAL, STRUCT_OR_UNION_LITERAL, SUBSCRIPT, SYSTEM_GUARD, UNARY, UNDEFINED_PROC, VARIABLE, HERE_OR_ROOT, PROC_NULL, SYSTEM_FUNC_CALL, REC_DOMAIN_LITERAL, REMOTE_REFERENCE, WILDCARD, NOTHING
	}

	/**
	 * @return The highest scope accessed by this expression. Null if no
	 *         variables accessed.
	 */
	Scope expressionScope();

	Scope lowestScope();

	/**
	 * 
	 * @return The type of this expression. For a primitive or variable, this is
	 *         the type of the primitive or variable. For a cast expression it
	 *         is the cast type. For operations it is the type of the operation
	 *         result.
	 */
	CIVLType getExpressionType();

	/**
	 * Returns the kind of this expression
	 * 
	 * @return The expression kind
	 */
	ExpressionKind expressionKind();

	/**
	 * Calculate the existence of dereferences in this expression
	 */
	void calculateDerefs();

	/**
	 * return true iff the expression has at least one dereferences of a certain
	 * pointer variable
	 * 
	 * @return True of False
	 */
	boolean hasDerefs();

	/**
	 * Analyzes if variables accessed by this expression are purely local
	 * 
	 * @param funcScope
	 *            The function scope of this expression
	 */
	void purelyLocalAnalysisOfVariables(Scope funcScope);

	/**
	 * @return True iff the expression accessed only purely-local variables
	 */
	boolean isPurelyLocal();

	/**
	 * Analyzes if this expression is purely local
	 */
	void purelyLocalAnalysis();

	/**
	 * Replace a certain conditional expression with a variable expression. Used
	 * when translating away conditional expressions with temporal variable
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
	 * Attempt to create a expression by replacing a certain conditional
	 * expression with a new expression, used when translating away conditional
	 * expressions without introduction temporal variable
	 * 
	 * @param oldExpression
	 *            The conditional expression
	 * @param newExpression
	 *            The new expression
	 * @return Null if nothing is changed, otherwise the new expression
	 */
	Expression replaceWith(ConditionalExpression oldExpression,
			Expression newExpression);

	/**
	 * Compute the set of variables visible from a certain scope that appear in
	 * an address-of expression. e.g., <code>(&a + &b)</code> returns
	 * <code>{a}</code> if <code>a</code> is in visible from the given scope
	 * while <code>b</code> invisible from the given scope.
	 * 
	 * @param scope
	 *            The scope to focus on.
	 * @return
	 */
	Set<Variable> variableAddressedOf(Scope scope);

	/**
	 * Compute the set of variables that appear in an address-of expression.
	 * e.g., <code>(&a + &b)</code> returns <code>{a, b}</code>.
	 * 
	 * @return
	 */
	Set<Variable> variableAddressedOf();

	/**
	 * The immutable constant value of this expression. NULL if the expression
	 * is not a constant.
	 * 
	 * @return the constant value of this expression. NULL if the expression is
	 *         not a constant.
	 */
	SymbolicExpression constantValue();

	/**
	 * Checks if this expression has a constant value, i.e., constantValue() !=
	 * NULL.
	 * 
	 * @return true iff this expression has a constant value.
	 */
	boolean hasConstantValue();

	/**
	 * Calculates the constant value of this expression.
	 * 
	 * @param universe
	 *            The symbolic universe to be used.
	 */
	void calculateConstantValue(SymbolicUniverse universe);

	/**
	 * checks if this expression contains the constant $here.
	 * 
	 * e.g.: s<$here would return true.
	 * 
	 * @return
	 */
	boolean containsHere();
}
