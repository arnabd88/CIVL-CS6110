package edu.udel.cis.vsl.civl.model.IF.statement;

import java.util.List;

import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.FunctionIdentifierExpression;

public interface ContractVerifyStatement extends Statement {

	/**
	 * TODO: get rid of it
	 * 
	 * @return The function being called.
	 */
	CIVLFunction function();

	/**
	 * @return The arguments to the function.
	 */
	List<Expression> arguments();

	/**
	 * TODO: get rid of this, but updates the function expression instead.
	 * 
	 * @param function
	 *            The function being called.
	 */
	void setFunction(FunctionIdentifierExpression function);

	/**
	 * @param arguments
	 *            The arguments to the function.
	 */
	void setArguments(List<Expression> arguments);

	/**
	 * Check if the statement is calling a system function.
	 * 
	 * @return
	 */
	boolean isSystemCall();

	Expression functionExpression();
}
