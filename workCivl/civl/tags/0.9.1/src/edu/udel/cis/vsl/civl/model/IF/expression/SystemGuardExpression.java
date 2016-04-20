package edu.udel.cis.vsl.civl.model.IF.expression;

/**
 * A system guard expression is a sudo guard expression for system function
 * calls. Its evaluation is actually done in the corresponding library executor.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public interface SystemGuardExpression extends Expression {
	/**
	 * The name of the library that the invoked function belongs to.
	 * 
	 * @return
	 */
	String library();

	/**
	 * The name of the invoked function.
	 * 
	 * @return
	 */
	String functionName();

	/**
	 * The list of arguments that this function call uses.
	 * 
	 * @return
	 */
	Expression[] arguments();
}
