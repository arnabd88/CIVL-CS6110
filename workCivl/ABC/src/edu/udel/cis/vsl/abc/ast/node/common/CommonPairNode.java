package edu.udel.cis.vsl.abc.ast.node.common;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.PairNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonPairNode<S extends ASTNode, T extends ASTNode> extends
		CommonASTNode implements PairNode<S, T> {

	public CommonPairNode(Source source, S left, T right) {
		super(source, left, right);
	}

	@SuppressWarnings("unchecked")
	@Override
	public S getLeft() {
		return (S) child(0);
	}

	@SuppressWarnings("unchecked")
	@Override
	public T getRight() {
		return (T) child(1);
	}

	@Override
	public void setLeft(S child) {
		setChild(0, child);
	}

	@Override
	public void setRight(T child) {
		setChild(1, child);
	}

	@Override
	protected void printBody(PrintStream out) {
	}

	@Override
	public PairNode<S, T> copy() {
		S left = getLeft();
		@SuppressWarnings("unchecked")
		S leftCopy = left == null ? null : (S) left.copy();
		T right = getRight();
		@SuppressWarnings("unchecked")
		T rightCopy = right == null ? null : (T) right.copy();

		return new CommonPairNode<S, T>(getSource(), leftCopy, rightCopy);
	}

	@Override
	public NodeKind nodeKind() {
		return NodeKind.PAIR;
	}
}
