package edu.udel.cis.vsl.abc.ast.node.IF.statement;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;

/**
 * A for loop, in addition to the expression and body that all loops possess,
 * has an initializer and incrementer.
 * 
 * The initializer can be either an expression or a declaration.
 * 
 * See C11 Sec. 6.8.5.
 * 
 * @author siegel
 * 
 */
public interface ForLoopNode extends LoopNode {

	/**
	 * Gets the initializer part of this for loop node. Note that this is an
	 * instance of either {@link ExpressionNode} or {@link DeclarationListNode}.
	 */
	ForLoopInitializerNode getInitializer();

	/**
	 * Sets the initializer part of this for loop node.
	 * 
	 * @param initNode
	 *            the initializer
	 */
	void setInitializer(ForLoopInitializerNode initNode);

	/**
	 * Gets the incrementer part of this for loop node.
	 * 
	 * @return incrementer
	 */
	ExpressionNode getIncrementer();

	/**
	 * Sets the incrementer part of this for loop node.
	 * 
	 * @param node
	 *            the incrementer
	 */
	void setIncrementer(ExpressionNode node);

	@Override
	ForLoopNode copy();

}
