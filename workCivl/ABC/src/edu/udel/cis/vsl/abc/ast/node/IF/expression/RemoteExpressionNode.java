package edu.udel.cis.vsl.abc.ast.node.IF.expression;

/**
 * A CIVL-C remote expression is used to reference a variable in another
 * process. Not yet implemented.
 * 
 * @author siegel
 * 
 */
public interface RemoteExpressionNode extends ExpressionNode {

	/**
	 * Gets the expression which yields the process on which the foreign
	 * variable resides.
	 * 
	 * @return the process expression
	 */
	ExpressionNode getProcessExpression();

	/**
	 * Sets the process expressions argument.
	 * 
	 * @param arg
	 *            the process expression argument
	 */
	void setProcessExpression(ExpressionNode arg);

	/**
	 * Gets the identifier node containing the name of the foreign variable.
	 * 
	 * @return the identifier for the name of the foreign variable
	 */
	IdentifierExpressionNode getIdentifierNode();

	/**
	 * Sets the identifier node argument.
	 * 
	 * @param arg
	 *            the identifier node argument
	 */
	void setIdentifierNode(IdentifierExpressionNode arg);

	@Override
	RemoteExpressionNode copy();

}
