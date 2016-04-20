package edu.udel.cis.vsl.civl.model.IF.contract;

import java.io.PrintStream;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

/**
 * A named behavior contains a name and assumptions in addition to those
 * components contained by {@link FunctionBehavior}. It is corresponding to the
 * named behavior block of an ACSL function contract.
 * 
 * @author Manchun Zheng
 *
 */
public interface NamedFunctionBehavior extends FunctionBehavior {

	/**
	 * Returns the name of this behavior.
	 * 
	 * @return
	 */
	String name();

	/**
	 * prints this behavior
	 * 
	 * @param prefix
	 * @param out
	 * @param isDebug
	 */
	void print(String prefix, PrintStream out, boolean isDebug);

	/**
	 * Returns the assumptions of this behavior.
	 * 
	 * @return
	 */
	Iterable<Expression> assumptions();

	/**
	 * Adds an assumption to this behavior.
	 * 
	 * @param assumption
	 */
	void addAssumption(Expression assumption);

	/**
	 * Returns the number of assumptions of this behavior.
	 * 
	 * @return
	 */
	int numAssumptions();
}
