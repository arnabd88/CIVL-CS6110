package edu.udel.cis.vsl.civl.model.IF;

import java.io.PrintStream;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;

/**
 * A fragment is a sequence of statements. It has a "pointer" to the start
 * location and a "pointer" to the last statement of the fragment.
 * 
 * @author Manchun Zheng
 * 
 */
public interface Fragment {

	/**
	 * Add a specified guard to the all statements of the start location. If a
	 * statement has an existing guard, then it will have a new guard which is a
	 * conjunction of the both. This method is used for translating a when
	 * statement, where it adds the guard of the when statement to the start
	 * location of its body fragment.
	 * 
	 * @param guard
	 *            The guard that is to be combined with
	 * @param factory
	 *            The model factory that provides some helper methods that are
	 *            useful in checking if an expression is True.
	 */
	void addGuardToStartLocation(Expression guard, ModelFactory factory);

	void addLastStatement(Statement statement);

	void addNewStatement(Statement statement);

	/**
	 * Combine two fragment in sequential order. <br>
	 * Precondition: <code>this.lastStatement == null</code>
	 * 
	 * @param next
	 *            the fragment that comes after the current fragment
	 * @return the sequential combination of both fragments
	 */
	Fragment combineWith(Fragment next);

	/**
	 * Check if the fragment is empty
	 * 
	 * @return true iff both the start location and the last statement are null
	 */
	boolean isEmpty();

	/**
	 * 
	 * @return The last statement of this fragment
	 */
	Statement lastStatement();

	/**
	 * Combine this fragment and another fragment in parallel, i.e., merge the
	 * start location, and add the last statement of both fragments as the last
	 * statement of the result fragment
	 * 
	 * @param parallel
	 *            the second fragment to be combined with <dt>
	 *            <b>Preconditions:</b>
	 *            <dd>
	 *            this.startLocation.id() === parallel.startLocation.id()
	 * 
	 * @return the new fragment after the combination
	 */
	Fragment parallelCombineWith(Fragment parallel);

	/**
	 * Print the fragment
	 * 
	 * @param out
	 *            the print stream
	 */
	void print(PrintStream out);

	/**
	 * Update the start location of this fragment
	 * 
	 * @param location
	 *            The new start location
	 */
	void setStartLocation(Location location);

	/**
	 * Update the last statement of this fragment
	 * 
	 * @param statement
	 *            The new last statement
	 */
	void setLastStatement(Statement statement);

	/**
	 * 
	 * @return The start location of this fragment
	 */
	Location startLocation();

	/**
	 * Update the start location with a new location
	 * 
	 * @param newLocation
	 *            the new start location
	 */
	void updateStartLocation(Location newLocation);

}
