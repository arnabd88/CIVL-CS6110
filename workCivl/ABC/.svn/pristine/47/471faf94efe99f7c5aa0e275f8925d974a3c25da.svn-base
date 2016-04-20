package edu.udel.cis.vsl.abc.ast.node.IF.statement;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;

public interface IfNode extends StatementNode {

	/**
	 * The condition controlling this "if" statement
	 * 
	 * @return the branch condition expression
	 */
	ExpressionNode getCondition();

	/**
	 * Returns the "true" branch statement--where control moves to if the
	 * condition evaluates to true.
	 * 
	 * @return the true branch statement
	 */
	StatementNode getTrueBranch();

	/**
	 * Returns the "else" (aka "false") branch. May be null (if this "if"
	 * statement has no "else" clause).
	 * 
	 * @return false branch, or null
	 */
	StatementNode getFalseBranch();

	@Override
	IfNode copy();

}
