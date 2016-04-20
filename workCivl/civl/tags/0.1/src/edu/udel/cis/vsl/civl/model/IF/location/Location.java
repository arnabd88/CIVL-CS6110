/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.location;

import java.io.PrintStream;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.Function;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;

/**
 * The parent of all locations.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface Location {
	/**
	 * @return The unique ID number of this location.
	 */
	public int id();

	/**
	 * @return The scope of this location.
	 */
	public Scope scope();

	/**
	 * @return The function containing this location.
	 */
	public Function function();

	/**
	 * @return The set of incoming statements.
	 */
	public Set<Statement> incoming();

	/**
	 * @return The set of outgoing statements.
	 */
	public Set<Statement> outgoing();

	/**
	 * Set the unique ID number of this location.
	 * 
	 * @param id
	 *            The unique ID number of this location.
	 */
	public void setId(int id);

	/**
	 * @param scope
	 *            The scope of this location.
	 */
	public void setScope(Scope scope);

	/**
	 * @param incoming
	 *            The set of incoming statements.
	 */
	public void setIncoming(Set<Statement> incoming);

	/**
	 * @param outgoing
	 *            The set of outgoing statements.
	 */
	public void setOutgoing(Set<Statement> outgoing);

	/**
	 * @param statement
	 *            A new incoming statement.
	 */
	public void addIncoming(Statement statement);

	/**
	 * @param statement
	 *            A new outgoing statement.
	 */
	public void addOutgoing(Statement statement);

	/**
	 * Print this location and all outgoing transitions.
	 * 
	 * @param prefix
	 *            The prefix string for all lines of this printout.
	 * @param out
	 *            The PrintStream to use for printing this location.
	 */
	public void print(String prefix, PrintStream out);

}
