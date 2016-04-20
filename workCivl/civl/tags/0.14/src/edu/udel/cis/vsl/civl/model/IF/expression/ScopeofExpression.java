package edu.udel.cis.vsl.civl.model.IF.expression;


/**
 * A scopeof expression is "$scopeof(expr)".
 * 
 * @author Manchun Zheng
 * 
 */
public interface ScopeofExpression extends Expression {
	LHSExpression argument();
}
