package edu.udel.cis.vsl.civl.model.IF.contract;

import java.util.List;

import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

/**
 * This represents a function call event of a <code>depends</code> clause.
 * 
 * @author Manchun Zheng
 *
 */
public interface CallEvent extends DependsEvent {

	/**
	 * The function (i.e., the callee) of this call event.
	 * 
	 * @return
	 */
	CIVLFunction function();

	/**
	 * Returns the arguments of the call event.
	 * 
	 * @return
	 */
	List<Expression> arguments();

	/**
	 * Returns the number of arguments of the call event.
	 * 
	 * @return
	 */
	int numArguments();

	/**
	 * Sets the callee of this event
	 * 
	 * @param function
	 */
	void setFunction(CIVLFunction function);

}
