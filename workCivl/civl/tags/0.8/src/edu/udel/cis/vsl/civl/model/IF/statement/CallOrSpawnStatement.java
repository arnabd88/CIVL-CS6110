/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.statement;

import java.util.List;

import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;

/**
 * A function call or spawn. Either of the form f(x) or else v=f(x).
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface CallOrSpawnStatement extends Statement {

	/**
	 * Is this a call (not spawn)?
	 * 
	 * @return true iff this is a call
	 */
	boolean isCall();

	/**
	 * Is this a spawn (not call)?
	 * 
	 * @return true iff this is a spawn
	 */
	boolean isSpawn();

	/**
	 * @return The left hand side expression if applicable. Else null.
	 */
	LHSExpression lhs();

	/**
	 * @return The function being called.
	 */
	CIVLFunction function();

	/**
	 * @return The arguments to the function.
	 */
	List<Expression> arguments();

	/**
	 * @param lhs
	 *            The left hand side expression if applicable. Else null.
	 */
	void setLhs(LHSExpression lhs);

	/**
	 * @param function
	 *            The function being called.
	 */
	void setFunction(CIVLFunction function);

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

	// /**
	// * complete the guard with the system guard if the current call is a
	// system
	// * function call.
	// */
	// void completeSystemGuard();

}
