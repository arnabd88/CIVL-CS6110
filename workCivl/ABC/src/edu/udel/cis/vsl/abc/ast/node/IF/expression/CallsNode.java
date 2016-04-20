package edu.udel.cis.vsl.abc.ast.node.IF.expression;

/**
 * Represents a CIVL-C <code>$calls</code> expression, which has the form
 * <code>$calls(f(e1,...,en))</code>. It is essentially a function call with the
 * keyword <code>$calls</code> prepended. This is also how it is represented: a
 * spawn node simply wraps a function call node.
 * 
 * @author siegel
 * 
 */
public interface CallsNode extends ExpressionNode {

	/**
	 * Returns the function call node, which is like removing the
	 * <code>$calls</code>.
	 * 
	 * @return the function call node
	 */
	FunctionCallNode getCall();

	/**
	 * Sets the function call node child to the given node.
	 * 
	 * @param call
	 *            the function call node
	 */
	void setCall(FunctionCallNode call);

	@Override
	CallsNode copy();

}
