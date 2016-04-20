package edu.udel.cis.vsl.abc.ast.node.IF.expression;

import edu.udel.cis.vsl.abc.ast.node.IF.statement.CompoundStatementNode;

/**
 * This represents a GNU C statement expression.
 * 
 * Section 6.1, GNU C language reference
 * 
 * A compound statement enclosed in parentheses may appear as an expression in
 * GNU C. This allows you to use loops, switches, and local variables within an
 * expression.
 * 
 * Recall that a compound statement is a sequence of statements surrounded by
 * braces; in this construct, parentheses go around the braces. For example:
 * 
 * <pre>
 * ({ int y = foo (); int z; if (y > 0) z = y; else z = - y; z; })
 * </pre>
 * 
 * is a valid (though slightly more complex than necessary) expression for the
 * absolute value of foo ().
 * 
 * The last thing in the compound statement should be an expression followed by
 * a semicolon; the value of this subexpression serves as the value of the
 * entire construct. (If you use some other kind of statement last within the
 * braces, the construct has type void, and thus effectively no value.)
 * 
 * @author Manchun Zheng
 *
 */
public interface StatementExpressionNode extends ExpressionNode {
	CompoundStatementNode getCompoundStatement();

	/**
	 * The last thing in the compound statement should be an expression followed
	 * by a semicolon; the value of this subexpression serves as the value of
	 * the entire construct.
	 * 
	 * @return the expression at the end of this construct
	 */
	ExpressionNode getExpression();
}
