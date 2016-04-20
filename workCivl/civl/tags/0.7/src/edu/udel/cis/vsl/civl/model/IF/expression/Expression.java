/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.expression;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.Sourceable;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLHeapType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * The parent of all expressions.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface Expression extends Sourceable {

	public enum ExpressionKind {
		ABSTRACT_FUNCTION_CALL, ADDRESS_OF, ARRAY_LITERAL, BINARY, BOOLEAN_LITERAL, BOUND_VARIABLE, CAST, CHAR_LITERAL, COND, DEREFERENCE, DERIVATIVE, DOT, DYNAMIC_TYPE_OF, INITIAL_VALUE, INTEGER_LITERAL, NULL_LITERAL, QUANTIFIER, REAL_LITERAL, RESULT, SELF, SIZEOF_TYPE, SIZEOF_EXPRESSION, STRING_LITERAL, STRUCT_LITERAL, SUBSCRIPT, UNARY, UNDEFINED_PROC, UNION_LITERAL, VARIABLE
	}

	/**
	 * @return The highest scope accessed by this expression. Null if no
	 *         variables accessed.
	 */
	Scope expressionScope();

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
	 * @param expressionScope
	 *            The highest scope accessed by this expression. Null if no
	 *            variables accessed.
	 */
	void setExpressionScope(Scope expressionScope);

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
	 * Compute the set of variables that are addressed of in the expression.
	 * e.g., &a + &b will returns {a, b}
	 * 
	 * @return
	 */
	Set<Variable> variableAddressedOf(Scope scope, CIVLHeapType heapType,
			CIVLType commType);

	Set<Variable> variableAddressedOf(CIVLHeapType heapType, CIVLType commType);
}
