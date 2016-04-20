package edu.udel.cis.vsl.abc.ast.node.IF.expression;

import edu.udel.cis.vsl.abc.ast.node.IF.PairNode;

/**
 * A CIVL-C derivative expression is a function call to the partial derivative
 * of an abstract function. It comprises a set of parameter-integer pairs which
 * encode the differential operator being applied to the function, and the
 * sequence of actual parameters which are the inputs to the resulting function.
 * 
 * @author zirkel
 * 
 */
public interface DerivativeExpressionNode extends ExpressionNode {

	/**
	 * The abstract function whose derivative is being taken.
	 * 
	 * @return The abstract function.
	 */
	ExpressionNode getFunction();

	/**
	 * Returns the number of actual arguments occurring in this derivative
	 * expression.
	 * 
	 * @return The number of actual arguments.
	 */
	int getNumberOfArguments();

	/**
	 * Returns the index-th argument, indexed from 0.
	 * 
	 * @return argument at position index, indexed from 0
	 */
	ExpressionNode getArgument(int index);

	/**
	 * Computes the number of parameters which have at least one partial
	 * derivative taken. Note that each parameter may have a partial taken more
	 * than once (e.g. <code>$D[rho,{x,3},{y,2}]</code>, so this is not the
	 * same thing as the total times a partial derivative is taken. That is, for
	 * <code>$D[rho,{x,3},{y,2}]</code>, this returns 2, not 5.
	 * 
	 * @return the number of parameters that have a partial of degree at least 1
	 */
	int getNumberOfPartials();

	/**
	 * Returns the (identifier, int) pair at the specified index in the list of
	 * partial derivatives.
	 * 
	 * @return the identifier-int pair at position <code>index</code>, indexed
	 *         from 0
	 */
	PairNode<IdentifierExpressionNode, IntegerConstantNode> getPartial(int index);

	@Override
	DerivativeExpressionNode copy();
}
