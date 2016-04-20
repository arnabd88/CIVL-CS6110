package edu.udel.cis.vsl.abc.ast.node.IF.label;

import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;

/**
 * Represents a label in a program. This can be either an ordinary label, which
 * is an identifier followed by a colon followed by a statement, and can be used
 * as the target of a <code>goto</code> (for example); or it can be a
 * <code>case</code> or <code>default</code> label used in a <code>switch</code>
 * statement.
 * 
 * @author siegel
 * 
 */
public interface LabelNode extends ASTNode {

	/**
	 * The statement which is preceded by a label (but not including the label).
	 * Note that the statement is not a child of this node. If it were, the AST
	 * would not be a tree.
	 * 
	 * @return the statement labeled
	 */
	StatementNode getStatement();

	/**
	 * Sets the value returned by {@link #getStatement()}.
	 * 
	 * @param statement
	 *            the statement labeled
	 */
	void setStatement(StatementNode statement);

	@Override
	LabelNode copy();

}
