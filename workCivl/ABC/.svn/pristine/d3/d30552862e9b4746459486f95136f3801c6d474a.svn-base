package edu.udel.cis.vsl.abc.ast.node.IF;

import java.util.List;

/**
 * A node in which all children have type <code>T</code>.
 */
public interface SequenceNode<T extends ASTNode> extends ASTNode, Iterable<T> {

	/**
	 * Appends the given node to the child list of this sequence node. In the
	 * pre-state, the given node must have no parent. In the post-state, the
	 * given node will have its parent set to this node.
	 * 
	 * @param child
	 *            a node of type <code>T</code> which does not currently have a
	 *            parent
	 * @return the index of the child after it is added, which equals the number
	 *         of children of this node in the prestate (i.e., before the method
	 *         executes)
	 */
	int addSequenceChild(T child);

	/**
	 * Returns the child at position i, indexed from 0. This may be
	 * <code>null</code>.
	 * 
	 * @param i
	 *            an integer in the range [0,n), where n is the number of
	 *            children of this sequence node
	 * 
	 * @return the child at index i, which may be <code>null</code>
	 */
	T getSequenceChild(int i);

	/**
	 * Sets the child at index i to the given node. The index i may be any
	 * nonnegative integer. If the index refers to a point beyond the current
	 * extent of the child list, <code>null</code> children are added until the
	 * list is long enough. Otherwise the old child at index i will be replaced
	 * by the new. If the old child was not <code>null</code>, it will become
	 * free, i.e., its parent field will be set to <code>null</code>.
	 * 
	 * @param i
	 *            a nonnegative integer
	 * @param child
	 *            a node of type <code>T</code> which does not currently have a
	 *            parent
	 * @return the old node in position i (could be <code>null</code>)
	 */
	T setSequenceChild(int i, T child);

	@Override
	SequenceNode<T> copy();

	@Override
	T removeChild(int index);

	/**
	 * Inserts a sequence of nodes into the child sequence of this node. Any
	 * children after the given index will be shifted up in index.
	 * 
	 * @param index
	 *            an integer in [0,numChildren]
	 * @param list
	 *            a non-null list of free nodes of type T, any of which may be
	 *            null
	 */
	void insertChildren(int index, List<T> list);

}
