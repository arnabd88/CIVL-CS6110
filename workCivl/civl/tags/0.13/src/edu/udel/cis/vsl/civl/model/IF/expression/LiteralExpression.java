/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.expression;

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
}
