package edu.udel.cis.vsl.abc.ast.node.IF;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.StringLiteralNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;

/**
 * A static assertion has syntax
 * <code>_Static_assert ( constant-expression , string-literal )</code>. It may
 * appear anywhere an external definition may appear, i.e., in the outermost
 * file scope. It is an assertion which is checked statically (i.e., at
 * "compile time"). The constant expression is evaluated. If it is 0, a
 * violation is reported.
 * 
 * @author siegel
 * 
 */
public interface StaticAssertionNode extends
		BlockItemNode {

	/**
	 * Gets the constant expression argument from this static assertion.
	 * 
	 * @return the constant expression argument
	 */
	ExpressionNode getExpression();

	/**
	 * Gests the string literal message argument from this static assertion.
	 * This is the message printed if the assertion is violated.
	 * 
	 * @return the string literal argument
	 */
	StringLiteralNode getMessage();

	@Override
	StaticAssertionNode copy();

}
