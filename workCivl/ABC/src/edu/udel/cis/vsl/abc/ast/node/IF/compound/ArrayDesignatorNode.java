package edu.udel.cis.vsl.abc.ast.node.IF.compound;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;

/**
 * An array designator specifies the index of an element of an array being
 * initialized.
 * 
 * @author siegel
 * 
 */
public interface ArrayDesignatorNode extends DesignatorNode {

	/**
	 * Gets the constant expression which yields the index to initialize.
	 * 
	 * @return array index expression
	 */
	ExpressionNode getIndex();

	/**
	 * Sets the index expression.
	 * 
	 * @param expression
	 *            a constant expression
	 */
	void setIndex(ExpressionNode expression);

	@Override
	ArrayDesignatorNode copy();
}
