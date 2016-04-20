/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.statement;

import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.Sourceable;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;

/**
 * The parent of all statements.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface Statement extends Sourceable {

	/**
	 * @return The location that is the source of this statement.
	 */
	Location source();

	/**
	 * @return The location that is the target of this statement.
	 */
	Location target();

	/**
	 * @return The boolean-valued guard expression for this statement.
	 */
	Expression guard();
	
	/**
	 * @return The model to which this statement belongs.
	 */
	Model model();

	/**
	 * @param source
	 *            the source to set
	 */
	void setSource(Location source);

	/**
	 * @param target
	 *            the target to set
	 */
	void setTarget(Location target);

	/**
	 * @param guard
	 *            the guard to set
	 */
	void setGuard(Expression guard);

	/**
	 * @param model The Model to which this statement belongs.
	 */
	void setModel(Model model);
	
	
	/**
	 * @return The highest scope accessed by this statement. Null if no
	 *         variables accessed.
	 */
	Scope statementScope();

	/**
	 * @param statementScope
	 *            The highest scope accessed by this statement. Null if no
	 *            variables accessed.
	 */
	void setStatementScope(Scope statementScope);
	
	/**
	 * return true iff the statement has at least one dereferences
	 * @return
	 */
	boolean hasDerefs();
	
	void caculateDerefs();

	/**
	 * if an &(var) is encountered, then var is considered as no purely local
	 * if a statement inside a function with fscope is accessing some variable
	 * that is declared in the scope vscope such that fscope.isDescendantOf(vscope),
	 * then that variable is not purely local
	 * @param funcScope the function scope of the statement
	 */
	void purelyLocalAnalysisOfVariables(Scope funcScope);
	
	boolean isPurelyLocal();
	
	void purelyLocalAnalysis();

}
