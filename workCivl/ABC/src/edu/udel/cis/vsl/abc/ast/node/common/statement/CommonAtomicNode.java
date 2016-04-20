package edu.udel.cis.vsl.abc.ast.node.common.statement;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.IF.DifferenceObject;
import edu.udel.cis.vsl.abc.ast.IF.DifferenceObject.DiffKind;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.AtomicNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

/**
 * An "atomic" statement has the form <code>$atomic body</code> or
 * <code>$atom body</code>, where body is a list of statements.
 * 
 * @author zheng
 * 
 */

public class CommonAtomicNode extends CommonStatementNode implements AtomicNode {

	/**
	 * True iff the atomic node is declared by <code>$atom</code>; otherwise, it
	 * is general atomic node starting with <code>$atomic</code>.
	 */
	private boolean isAtom = false;

	/**
	 * Constructor
	 * 
	 * @param source
	 * @param body
	 */
	public CommonAtomicNode(Source source, boolean isAtom, StatementNode body) {
		super(source, body);
		this.isAtom = isAtom;
	}

	@Override
	public StatementKind statementKind() {
		return StatementKind.ATOMIC;
	}

	@Override
	public StatementNode getBody() {
		return (StatementNode) child(0);
	}

	@Override
	public AtomicNode copy() {
		StatementNode body = getBody();
		StatementNode bodyCopy = body == null ? null : body.copy();

		return new CommonAtomicNode(getSource(), this.isAtom, bodyCopy);
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("atomic");
	}

	@Override
	public boolean isAtom() {
		return this.isAtom;
	}

	@Override
	protected DifferenceObject diffWork(ASTNode that) {
		if (that instanceof AtomicNode)
			if (this.isAtom == ((AtomicNode) that).isAtom())
				return null;
			else
				return new DifferenceObject(this, that, DiffKind.OTHER,
						"different atom/atomic specifier");
		return new DifferenceObject(this, that);
	}

	@Override
	public void setBody(StatementNode body) {
		setChild(0, body);
	}
}
