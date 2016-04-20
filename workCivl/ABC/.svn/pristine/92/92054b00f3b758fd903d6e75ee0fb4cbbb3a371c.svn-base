package edu.udel.cis.vsl.abc.transform.common;

import java.util.List;

import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;

/**
 * An ExprTriple is an SETriple for which the node is an expression, i.e.,
 * instance of ExpressionNode.
 * 
 * @author zirkel
 */
public class ExprTriple extends SETriple {

	/**
	 * 
	 * @param before
	 *            The block items that come before this expression.
	 * @param expression
	 *            The side effect free expression.
	 * @param after
	 *            The block items that come after this expression.
	 */
	public ExprTriple(List<BlockItemNode> before, ExpressionNode expression,
			List<BlockItemNode> after) {
		super(before, expression, after);
	}

	public ExprTriple(ExpressionNode expression) {
		super(expression);
	}

	/**
	 * @return the expression.
	 */
	@Override
	public ExpressionNode getNode() {
		return (ExpressionNode) node;
	}

	/**
	 * @param expression
	 *            The side effect free expression.
	 */
	@Override
	public void setNode(ASTNode expression) {
		if (expression != null) {
			assert expression instanceof ExpressionNode;
			expression.remove();
		}
		this.node = expression;
	}
}
