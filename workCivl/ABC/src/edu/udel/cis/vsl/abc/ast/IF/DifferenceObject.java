package edu.udel.cis.vsl.abc.ast.IF;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.PragmaNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.BasicTypeNode;

public class DifferenceObject {
	public enum DiffKind {
		/**
		 * Two basic type nodes with different basic type kind.
		 */
		BASIC_TYPE_KIND,
		/**
		 * Two nodes with different node kind.
		 */
		KIND,
		/**
		 * This node is null while that node is not.
		 */
		THIS_NULL,
		/**
		 * That node is null while this node is not.
		 */
		THAT_NULL,
		/**
		 * Two nodes don't agree on the number of children.
		 */
		NUM_CHILDREN,
		/**
		 * Two identifier nodes with different names.
		 */
		IDENTIFIER_NAME,
		/**
		 * Two pragma nodes don't agree on the number of tokens.
		 */
		PRAGMA_NUM_TOKENS,
		/**
		 * Two constant nodes of the same type don't agree on their values.
		 */
		CONSTANT_VALUE,
		/**
		 * Other kinds, explanation is user-specified.
		 */
		OTHER
	}

	private ASTNode thisNode;
	private ASTNode thatNode;
	private String message = null;
	private DiffKind kind;

	private String getNodeInfo(ASTNode node) {
		StringBuffer buf = new StringBuffer();

		if (node == null) {
			buf.append("NULL");
			return buf.toString();
		} else
			buf.append(node.prettyRepresentation());
		buf.append("    at ");
		buf.append(node.getSource().getSummary(false));
		return buf.toString();
	}

	public DifferenceObject(ASTNode node, boolean isThisNull) {
		StringBuffer buf = new StringBuffer();

		if (isThisNull) {
			thatNode = node;
			kind = DiffKind.THIS_NULL;
			buf.append("This node is NULL while that node is not.\n");
			buf.append("That node: ");
			buf.append(this.getNodeInfo(thatNode));
		} else {
			thisNode = node;
			kind = DiffKind.THAT_NULL;
			buf.append("This node is not NULL while that node is NULL.\n");
			buf.append("This node: ");
			buf.append(this.getNodeInfo(thatNode));
		}
		message = buf.toString();
	}

	public DifferenceObject(ASTNode thisNode, ASTNode thatNode) {
		StringBuffer buf = new StringBuffer();

		this.thisNode = thisNode;
		this.thatNode = thatNode;
		this.kind = DiffKind.KIND;
		buf.append("Two inequivalent nodes are encountered.\n");
		buf.append("This node: ");
		buf.append(this.getNodeInfo(thisNode));
		buf.append("\n");
		buf.append("That node: ");
		buf.append(this.getNodeInfo(thatNode));
		this.message = buf.toString();
	}

	public DifferenceObject(ASTNode thisNode, ASTNode thatNode, DiffKind kind) {
		StringBuffer buf = new StringBuffer();

		this.thisNode = thisNode;
		this.thatNode = thatNode;
		this.kind = kind;
		buf.append("Two inequivalent nodes are encountered.\nDifferent kind: ");
		buf.append(kind);
		buf.append("\n");
		switch (kind) {
		case BASIC_TYPE_KIND: {
			BasicTypeNode thisType = (BasicTypeNode) thisNode, thatType = (BasicTypeNode) thatNode;

			buf.append("This node: type ");
			buf.append(thisType.getBasicTypeKind());
			buf.append("\n");
			buf.append("  ");
			buf.append(this.getNodeInfo(thisNode));
			buf.append("\n");
			buf.append("That node: type ");
			buf.append(thatType.getBasicTypeKind());
			buf.append("  ");
			buf.append(this.getNodeInfo(thatNode));
			break;
		}
		case NUM_CHILDREN:
			buf.append("This node:  ");
			buf.append(thisNode.numChildren());
			buf.append(" children \n");
			buf.append("  ");
			buf.append(this.getNodeInfo(thisNode));
			buf.append("\n");
			buf.append("That node: ");
			buf.append(thatNode.numChildren());
			buf.append(" children");
			buf.append("  ");
			buf.append(this.getNodeInfo(thatNode));
			break;
		case IDENTIFIER_NAME:
			buf.append("This node: name ");
			buf.append(((IdentifierNode) thisNode).name());
			buf.append("\n  ");
			buf.append(this.getNodeInfo(thisNode));
			buf.append("\n");
			buf.append("That node: name ");
			buf.append(((IdentifierNode) thatNode).name());
			buf.append("  ");
			buf.append(this.getNodeInfo(thatNode));
			break;
		case PRAGMA_NUM_TOKENS:
			buf.append("This node:  ");
			buf.append(((PragmaNode) thisNode).getNumTokens());
			buf.append(" tokens \n  ");
			buf.append(this.getNodeInfo(thisNode));
			buf.append("\n");
			buf.append("That node: ");
			buf.append(((PragmaNode) thatNode).getNumTokens());
			buf.append(" tokens\n  ");
			buf.append(this.getNodeInfo(thatNode));
			break;
		default:
			buf.append("This node: ");
			if (thisNode != null)
				buf.append(this.getNodeInfo(thisNode));
			else
				buf.append("NULL");
			buf.append("\n");
			buf.append("That node: ");
			if (thatNode != null)
				buf.append(this.getNodeInfo(thatNode));
			else
				buf.append("NULL");
		}
		this.message = buf.toString();
	}

	public DifferenceObject(ASTNode thisNode, ASTNode thatNode, DiffKind other,
			String message) {
		this.thisNode = thisNode;
		this.thatNode = thatNode;
		this.message = message;
	}

	public DiffKind getDiffKind() {
		return this.kind;
	}

	public ASTNode getThisNode() {
		return thisNode;
	}

	public ASTNode getThatNode() {
		return thatNode;
	}

	public String getMessage() {
		return message;
	}

	public void print(PrintStream out) {
		out.println(this.getMessage());
	}

	@Override
	public String toString() {
		return this.message;
	}
}
