package edu.udel.cis.vsl.civl.model.IF.expression;

import java.util.List;

import edu.udel.cis.vsl.civl.model.IF.AbstractFunction;

/**
 * An expression representing a call of an abstract function.
 * 
 * Since abstract functions are uninterpreted, a call to one can always be
 * treated as side-effect free (provided parameters are side-effect free). Thus
 * we can have this in an expression.
 * 
 * @author zirkel
 * 
 */
public interface AbstractFunctionCallExpression extends Expression {

	/**
	 * 
	 * @return The abstract function being called.
	 */
	AbstractFunction function();
	
	/**
	 * @return The arguments to the function.
	 */
	List<Expression> arguments();

}
