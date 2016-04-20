/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.expression;

import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * The parent of all literal expressions.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface LiteralExpression extends Expression {
	public enum LiteralKind {
		ARRAY, BOOLEAN, CHAR, INTEGER, REAL, STRING, STRUCT_OR_UNION, DOMAIN
	}

	LiteralKind literalKind();

	/**
	 * Directly set a symbolic expression as value of this literal expression
	 * 
	 * @param value
	 *            The symbolic expression of the constant value of this literal
	 *            expression
	 */
	void setLiteralConstantValue(SymbolicExpression value);
}
