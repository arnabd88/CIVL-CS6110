/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.location;

import java.io.PrintStream;

import edu.udel.cis.vsl.civl.err.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.Sourceable;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;

/**
 * The parent of all locations.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface Location extends Sourceable {
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
	public CIVLFunction function();

	/**
	 * @return The set of incoming statements.
	 */
	public Iterable<Statement> incoming();

	/**
	 * @return The set of outgoing statements.
	 */
	public Iterable<Statement> outgoing();

	
	/**
	 * @return The number of outgoing statements.
	 */
	public int getNumOutgoing();
	
	/**
	 * @return The number of incoming statements.
	 */
	public int getNumIncoming();
	
	public Statement getOutgoing(int i);
	
	public Statement getIncoming(int i);
	
	// TODO: javadocs
	/**
	 * Returns the sole outgoing statement from this location.
	 * 
	 * @return the outgoing statement
	 * @throws CIVLInternalException
	 *             if the number of outgoing statements from this location is
	 *             not 1
	 */
	public Statement getSoleOutgoing();

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
//
//	/**
//	 * @param incoming
//	 *            The set of incoming statements.
//	 */
//	public void setIncoming(Set<Statement> incoming);
//
//	/**
//	 * @param outgoing
//	 *            The set of outgoing statements.
//	 */
//	public void setOutgoing(Set<Statement> outgoing);

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
	
	public boolean isPurelyLocal();

	public void purelyLocalAnalysis();

	void removeOutgoing(Statement statement);

	void removeIncoming(Statement statement);

}
