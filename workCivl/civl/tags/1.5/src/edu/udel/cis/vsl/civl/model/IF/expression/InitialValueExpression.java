package edu.udel.cis.vsl.civl.model.IF.expression;

import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * An expression yielding the initial value of a variable.
 * 
 * @author siegel
 * 
 */
public interface InitialValueExpression extends Expression {

	Variable variable();

}
