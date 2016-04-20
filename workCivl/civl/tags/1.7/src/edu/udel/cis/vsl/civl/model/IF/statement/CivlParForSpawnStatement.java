package edu.udel.cis.vsl.civl.model.IF.statement;

import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;

/**
 * This represents the first part of a $parfor construct, i.e., spawning
 * processes according the specified domain.
 * 
 * @author Manchun Zheng (zmanchun)
 *
 */
public interface CivlParForSpawnStatement extends Statement {

	/**
	 * returns the function to be executed by the spawned processes, which is
	 * equivalent to the body of the $parfor.
	 * 
	 * @return the function to be executed by the spawned processes, which is
	 *         equivalent to the body of the $parfor.
	 */
	CIVLFunction parProcFunction();

	/**
	 * returns the domain according to which processes will be spawned.
	 * 
	 * @return the domain according to which processes will be spawned.
	 */
	Expression domain();

	/**
	 * returns the dimension of the domain
	 * 
	 * @return the dimension of the domain
	 */
	int dimension();

	/**
	 * returns the variable that represents the size of the domain, i.e., how
	 * many elements are contained in the domain. The actual value of this
	 * variable is to be updated during the execution of this
	 * CivlParForSpawnStatement.
	 * 
	 * @return the variable that represents the size of the domain
	 */
	VariableExpression domSizeVar();

	/**
	 * returns the variable that represents the array of process references of
	 * processes spawned by this CivlParForSpawnStatement.
	 * 
	 * @return the variable that represents the array of references of the
	 *         spawned processes.
	 */
	VariableExpression parProcsVar();

	/**
	 * updates the function which will be executed by spawned processes.
	 * 
	 * @param function
	 *            the function equivalent to the body of the $parfor
	 */
	void setParProcFunction(CIVLFunction function);
}
