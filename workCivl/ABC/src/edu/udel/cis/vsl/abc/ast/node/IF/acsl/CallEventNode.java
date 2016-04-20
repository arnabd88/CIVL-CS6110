package edu.udel.cis.vsl.abc.ast.node.IF.acsl;

import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;

/**
 * An event that represents a function call with certain arguments, which is a
 * kind of Depends Event. It has the following syntax:
 * 
 * <pre>
 * \call(func, x0, x1, x2, ...);
 * </pre>
 * 
 * @author Manchun Zheng
 *
 */
public interface CallEventNode extends DependsEventNode {

	/**
	 * the name of the function of this call event
	 * 
	 * @return
	 */
	IdentifierExpressionNode getFunction();

	/**
	 * the arguments of the function call
	 * 
	 * @return
	 */
	SequenceNode<ExpressionNode> arguments();

	@Override
	CallEventNode copy();
}
