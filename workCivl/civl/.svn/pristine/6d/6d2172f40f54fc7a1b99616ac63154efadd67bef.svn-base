package edu.udel.cis.vsl.civl.model.IF.expression;

import java.util.List;

/**
 * A function pointer guard expression is the guard expression of a function
 * call with a function pointer. A compile time, the actual function is unknown,
 * and thus we need this expression, in case the function pointer points to a
 * system function.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public interface FunctionGuardExpression extends Expression {
	/**
	 * Returns the function expression of the corresponding call statement of
	 * this guard expression.
	 * 
	 * @return
	 */
	Expression functionExpression();

	/**
	 * Returns the list of arguments of the corresponding function call
	 * statement.
	 * 
	 * @return
	 */
	List<Expression> arguments();
}
