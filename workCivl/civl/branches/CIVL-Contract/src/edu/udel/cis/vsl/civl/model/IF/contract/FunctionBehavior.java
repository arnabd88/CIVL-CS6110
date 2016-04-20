package edu.udel.cis.vsl.civl.model.IF.contract;

import java.io.PrintStream;

import edu.udel.cis.vsl.civl.model.IF.Sourceable;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

/**
 * This represents a non-named behavior of the ACSL function contract. It
 * contains the common components of the default behavior and any named behavior
 * of a function contract.
 * 
 * @author Manchun Zheng
 *
 */
public interface FunctionBehavior extends Sourceable {

	/**
	 * Returns the preconditions of this behavior.
	 * 
	 * @return
	 */
	Iterable<Expression> requirements();

	/**
	 * Returns the postconditions of this behavior.
	 * 
	 * @return
	 */
	Iterable<Expression> ensurances();

	/**
	 * Returns the assigns clause of this behavior.
	 * 
	 * @return
	 */
	Iterable<Expression> assignsMemoryUnits();

	/**
	 * Returns the reads clause of this behavior.
	 * 
	 * @return
	 */
	Iterable<Expression> readsMemoryUnits();

	/**
	 * Returns the depends events of this behavior.
	 * 
	 * @return
	 */
	Iterable<DependsEvent> dependsEvents();

	/**
	 * Does this function reads nothing? That is, is there a
	 * <code>reads \nothing;</code> clause in the contract.
	 * 
	 * @return
	 */
	boolean readsNothing();

	/**
	 * Does this function assigns nothing? That is, is there a
	 * <code>assigns \nothing;</code> clause in the contract.
	 * 
	 * @return
	 */
	boolean assignsNothing();

	/**
	 * Is this function depending on nothing?
	 * 
	 * @return
	 */
	boolean dependsNoact();

	/**
	 * Is this function depending on anything?
	 * 
	 * @return
	 */
	boolean dependsAnyact();

	/**
	 * When a <code>reads \nothing;</code> clause appears, sets the function
	 * behavior to be reading nothing. <br>
	 * Precondition: {@link #numReadsClauses()}==0;
	 */
	void setReadsNothing();

	/**
	 * When a <code>assigns \nothing;</code> clause appears, sets the function
	 * behavior to be assigning nothing. <br>
	 * Precondition: {@link #numAssignsClauses()}==0;
	 */
	void setAssingsNothing();

	/**
	 * When a <code>depends \noact;</code> clause appears, sets the function
	 * behavior to be depending on nothing.<br>
	 * Precondition: {@link #numDependsEvents()}==0 && {@link #dependsAnyact()
	 * ==false};
	 */
	void setDependsNoact();

	/**
	 * When a <code>depends \anyact;</code> clause appears, sets the function
	 * behavior to be depending on anything.<br>
	 * Precondition: {@link #dependsNoact()==false};
	 */
	void setDependsAnyact();

	/**
	 * Returns the precondition of this behavior.
	 * 
	 * @param condition
	 */
	void addPrecondition(Expression condition);

	/**
	 * Returns the post condition of this behavior.
	 * 
	 * @param condition
	 */
	void addPostcondition(Expression condition);

	/**
	 * Add an assigns clause to this behavior.
	 * 
	 * @param assigns
	 */
	void addAssignsMemoryUnit(Expression mu);

	/**
	 * Add a reads clause to this behavior.
	 * 
	 * @param reads
	 */
	void addReadsMemoryUnit(Expression mu);

	/**
	 * Add a depends event to this behavior. <br>
	 * Precondition: {@link #dependsNoact()}==false;
	 * 
	 * @param depends
	 */
	void addDependsEvent(DependsEvent dependsEvent);

	/**
	 * Returns the number of preconditions of this behavior.
	 * 
	 * @return
	 */
	int numRequirements();

	/**
	 * Returns the number of postconditions of this behavior.
	 * 
	 * @return
	 */
	int numEnsurances();

	/**
	 * Returns the number of assigns clauses of this behavior.
	 * 
	 * @return
	 */
	int numAssignsMemoryUnits();

	/**
	 * Returns the number of reads clauses of this behavior.
	 * 
	 * @return
	 */
	int numReadsMemoryUnits();

	/**
	 * Returns the number of depends events of this behavior.
	 * 
	 * @return
	 */
	int numDependsEvents();

	/**
	 * Prints this behavior
	 * 
	 * @param subPrefix
	 * @param out
	 * @param isDebug
	 */
	void print(String prefix, PrintStream out, boolean isDebug);

	/**
	 * clears the depends events of this behavior.
	 */
	void clearDependsEvents();

}
