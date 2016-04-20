package edu.udel.cis.vsl.abc.ast.node.IF.expression;

/**
 * Represents a CIVL-C <code>$spawn</code> expression, which has the form
 * <code>$spawn f(e1,...,en)</code>. It is essentially a function call with the
 * keyword <code>$spawn</code> prepended. This is also how it is represented: a
 * spawn node simply wraps a function call node.
 * 
 * @author siegel
 * 
 */
public interface SpawnNode extends ExpressionNode {

	/**
	 * Returns the function call node, which is like removing the
	 * <code>$spawn</code>.
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
	SpawnNode copy();

}
