package edu.udel.cis.vsl.civl.model.IF.expression;

/**
 * An expression of the form "sizeof(e)" where e is an expression.
 * 
 * @author siegel
 * 
 */
public interface SizeofExpression extends Expression {

	Expression getArgument();

}
