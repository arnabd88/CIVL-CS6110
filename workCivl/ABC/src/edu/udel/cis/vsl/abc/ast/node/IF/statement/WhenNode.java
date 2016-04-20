package edu.udel.cis.vsl.abc.ast.node.IF.statement;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;

/**
 * Represents a CIVL-C guarded command. A <code>$when</code> statement has the
 * form <code>$when (guard) body</code>, where guard is a boolean-valued
 * expression and body is a statement.
 * 
 * @author siegel
 * 
 */
public interface WhenNode extends StatementNode {

	/**
	 * The guard: a boolean expression which must hold in order for the body to
	 * be executed.
	 * 
	 * @return the guard
	 */
	ExpressionNode getGuard();

	/**
	 * The body of this <code>$when</code> statement.
	 * 
	 * @return the body
	 */
	StatementNode getBody();

	@Override
	WhenNode copy();

}
