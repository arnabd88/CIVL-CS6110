/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.expression;

/**
 * The ternary conditional expression ("?" in C).
 * 
 * @author zirkel
 * 
 */
public interface ConditionalExpression extends Expression {

	/**
	 * 
	 * @return The condition being evaluated in this ternary expression.
	 */
	Expression getCondition();

	/**
	 * 
	 * @return The expression returned if the condition evaluates to true.
	 */
	Expression getTrueBranch();

	/**
	 * 
	 * @return The expression returned if the condition evaluates to false.
	 */
	Expression getFalseBranch();

}
