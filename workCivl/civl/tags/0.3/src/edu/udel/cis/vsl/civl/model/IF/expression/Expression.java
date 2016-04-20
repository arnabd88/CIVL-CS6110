/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.expression;

import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.Sourceable;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;

/**
 * The parent of all expressions.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface Expression extends Sourceable {

	public enum ExpressionKind {
		ADDRESS_OF,
		BINARY,
		BOOLEAN_LITERAL,
		CAST,
		COND,
		DEREFERENCE,
		DOT,
		DYNAMIC_TYPE_OF,
		INITIAL_VALUE,
		INTEGER_LITERAL,
		NULL_LITERAL,
		REAL_LITERAL,
		RESULT,
		SELF,
		SIZEOF_TYPE,
		SIZEOF_EXPRESSION,
		STRING_LITERAL,
		SUBSCRIPT,
		UNARY,
		VARIABLE
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

	/** Returns the kind of this expression */
	ExpressionKind expressionKind();

	/**
	 * @param expressionScope
	 *            The highest scope accessed by this expression. Null if no
	 *            variables accessed.
	 */
	void setExpressionScope(Scope expressionScope);
}
