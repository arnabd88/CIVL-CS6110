package edu.udel.cis.vsl.abc.transform.common;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;

/**
 * A side effect triple is used by the side effect remover. When removing side
 * effects from an AST node, the result is a side effect free version of the
 * node, together with (possibly empty) lists of statements that should come
 * before or after the use of the node.
 * 
 * @author Timothy K. Zirkel
 * @author Stephen F. Siegel
 */
public class SETriple {

	protected List<BlockItemNode> before, after;

	protected ASTNode node;

	/**
	 * 
	 * @param before
	 *            The block items that come before this expression.
	 * @param expression
	 *            The side effect free expression.
	 * @param after
	 *            The block items that come after this expression.
	 */
	public SETriple(List<BlockItemNode> before, ASTNode node,
			List<BlockItemNode> after) {
		this.before = before;
		this.node = node;
		if (node != null)
			node.remove();
		this.after = after;
	}

	public SETriple(ASTNode node) {
		this(new LinkedList<BlockItemNode>(), node,
				new LinkedList<BlockItemNode>());
	}

	/**
	 * @return The block items that come before this expression.
	 */
	public List<BlockItemNode> getBefore() {
		return before;
	}

	/**
	 * @return The block items that come after this expression.
	 */
	public List<BlockItemNode> getAfter() {
		return after;
	}

	/**
	 * @return the expression.
	 */
	public ASTNode getNode() {
		return node;
	}

	/**
	 * @param before
	 *            The block items that come before this expression.
	 */
	public void setBefore(List<BlockItemNode> before) {
		this.before = before;
	}

	/**
	 * @param after
	 *            The block items that come after this expression.
	 */
	public void setAfter(List<BlockItemNode> after) {
		this.after = after;
	}

	/**
	 * @param expression
	 *            The side effect free expression.
	 */
	public void setNode(ASTNode node) {
		this.node = node;
	}

	public boolean isTrivial() {
		return before.isEmpty() && after.isEmpty();
	}

	public void addAfter(BlockItemNode item) {
		after.add(item);
	}

	public void addBefore(BlockItemNode item) {
		before.add(item);
	}

	public void addAllAfter(Collection<BlockItemNode> items) {
		after.addAll(items);
	}

	public void addAllBefore(Collection<BlockItemNode> items) {
		before.addAll(items);
	}

	@Override
	public String toString() {
		StringBuffer result = new StringBuffer("[");
		boolean first = true;

		for (BlockItemNode item : before) {
			if (first)
				first = false;
			else
				result.append(',');
			result.append(item.toString());
		}
		result.append(" | ");
		result.append(node.toString());
		result.append(" | ");
		first = true;
		for (BlockItemNode item : after) {
			if (first)
				first = false;
			else
				result.append(',');
			result.append(item.toString());
		}
		result.append("]");
		return result.toString();
	}

}
