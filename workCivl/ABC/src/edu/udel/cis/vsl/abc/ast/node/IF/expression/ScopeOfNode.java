package edu.udel.cis.vsl.abc.ast.node.IF.expression;

/**
 * Represents a CIVL-C scope-of expression, which has the form
 * <code>$scopeof(lhs)</code>, where <code>lhs</code> is a left-hand-side
 * expression. This returns the dynamic scope (a value of type
 * <code>$scope</code>) which contains the memory unit specified by
 * <code>lhs</code>.
 * 
 * @author siegel
 * 
 */
public interface ScopeOfNode extends ExpressionNode {

	/**
	 * Returns the argument (<code>lhs</code>) of this scope-of expression.
	 * 
	 * @return the argument
	 */
	ExpressionNode expression();

	/**
	 * Sets the argument of this scope-of expression
	 * 
	 * @param expr
	 *            the argument
	 */
	void setExpression(ExpressionNode expr);

}
