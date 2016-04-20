package edu.udel.cis.vsl.abc.ast.node.IF;

/** A node with two children, the first of type S and the second of type T. */
public interface PairNode<S extends ASTNode, T extends ASTNode> extends ASTNode {

	/** Returns the left child. */
	S getLeft();

	/** Returns the right child. */
	T getRight();

	/** Set the left child. */
	void setLeft(S child);

	/** Set the right child. */
	void setRight(T child);

	@Override
	PairNode<S, T> copy();
}
