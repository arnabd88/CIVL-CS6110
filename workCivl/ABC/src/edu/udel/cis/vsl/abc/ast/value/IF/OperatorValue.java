package edu.udel.cis.vsl.abc.ast.value.IF;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;

public interface OperatorValue extends Value {

	Operator getOperator();

	/**
	 * Returns the number of arguments in this operator expression.
	 * 
	 * @return the number of arguments
	 */
	int getNumberOfArguments();

	/**
	 * Returns the index-th argument, indexed from 0. Beware: the argument index
	 * and the child index are off by one! So, argument 0 is child 1. That is
	 * because child 0 is the operator.
	 */
	Value getArgument(int index);

}
