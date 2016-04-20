/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.location;

import java.io.PrintStream;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.Sourceable;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * The parent of all locations.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface Location extends Sourceable {

	/**
	 * Atomic flags of a location:
	 * <ul>
	 * <li>NONE: no $atomic/$atom boundary;</li>
	 * <li>ATOMIC_ENTER/ATOM_ENTER: the location is the starting point of an
	 * $atomic/$atom block;</li>
	 * <li>ATOMIC_EXIT/ATOM_EXIT: the location is the ending point of an
	 * $atomic/$atom block.</li>
	 * </ul>
	 * 
	 * @author Manchun Zheng
	 * 
	 */
	public enum AtomicKind {
		NONE, ATOMIC_ENTER, ATOMIC_EXIT, ATOM_ENTER, ATOM_EXIT
	}

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
	 * @return The iterable object of incoming statements.
	 */
	public Iterable<Statement> incoming();

	/**
	 * @return The iterable object of outgoing statements.
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

	/**
	 * 
	 * @param i
	 *            index of the statement
	 * @return The i'th outgoing statement
	 */
	public Statement getOutgoing(int i);

	/**
	 * 
	 * @param i
	 *            index of the statement
	 * @return The i'th incoming statement
	 */
	public Statement getIncoming(int i);

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
	 * @param isDebug
	 *            True iff the debugging option is enabled
	 */
	public void print(String prefix, PrintStream out, boolean isDebug);

	/**
	 * 
	 * @return true iff the location is purely local
	 */
	public boolean isPurelyLocal();

	/**
	 * Analyze if the location is purely local
	 */
	public void purelyLocalAnalysis();

	/**
	 * Remove a certain outgoing statement
	 * 
	 * @param statement
	 *            The outgoing statement to be removed
	 */
	void removeOutgoing(Statement statement);

	/**
	 * Remove a certain incoming statement
	 * 
	 * @param statement
	 *            The incoming statement to be removed
	 */
	void removeIncoming(Statement statement);

	/**
	 * This location is the start location of a certain atomic block
	 * 
	 * @param deterministic
	 *            True iff the atomic block is a $datomic block
	 */
	void setEnterAtomic(boolean deterministic);

	/**
	 * This location is the end location of a certain atomic block
	 * 
	 * @param deterministic
	 *            True iff the atomic block is a $datomic block
	 */
	void setLeaveAtomic(boolean deterministic);

	/**
	 * Check if the location is entering a deterministic atomic block.
	 * 
	 * @return true iff the location is entering a deterministic atomic block.
	 * 
	 */
	boolean enterAtom();

	/**
	 * Check if the location is entering a general atomic block.
	 * 
	 * @return true iff the location is entering a general atomic block.
	 * 
	 */
	boolean enterAtomic();

	/**
	 * 
	 * @return true iff the location is leaving a deterministic atomic block
	 */
	boolean leaveAtom();

	/**
	 * 
	 * @return true iff the location is leaving a general atomic block
	 */
	boolean leaveAtomic();

	/**
	 * Result might be:
	 * <ol>
	 * <li>NONE: a normal location</li>
	 * <li>ENTER: the start location of an $atomic block</li>
	 * <li>LEAVE: the end location of an $atomic block</li>
	 * <li>DENTER: the start location of an $atom block</li>
	 * <li>LEAVE: the end location of an $atom block</li>
	 * </ol>
	 * 
	 * @return the atomic kind of the location
	 */
	AtomicKind atomicKind();

	/**
	 * This is different from isPurelyLocal(), because the latter is more
	 * restricted. Because the latter requires the location have exactly one
	 * incoming edge in order to avoid loop.
	 * 
	 * @return True iff every outgoing statement is purely local
	 */
	boolean allOutgoingPurelyLocal();

	/**
	 * Analyze each outgoing statement to see if they are purely local
	 */
	void purelyLocalAnalysisForOutgoing();

	/**
	 * 
	 * @return True if this location is possible to form a loop
	 */
	boolean isLoopPossible();

	/**
	 * During the translation of AST node into CIVL model, it is possible to
	 * know if a location with more than one incoming statement possible to be a
	 * loop location
	 * 
	 * @param possible
	 *            The value to be used to mark whether this location is possible
	 *            to be a loop location or not
	 */
	void setLoopPossible(boolean possible);

	/**
	 * Static analysis for possible loops form by this location
	 * 
	 * @return
	 */
	void loopAnalysis();

	/**
	 * The impact scope of a location is required in the enabler when an
	 * atomic/atom block is encountered, in which case the impact scope of all
	 * statements in the atomic block should be considered.
	 * 
	 * @return
	 */
	Scope impactScopeOfAtomicOrAtomBlock();

	/**
	 * set the impact scope of a location, only called when this.AtomicKind ==
	 * ATOM_ENTER or ATOMIC_ENTER.
	 * 
	 * @return
	 */
	void setImpactScopeOfAtomicOrAtomBlock(Scope scope);

	void computeWritableVariables(Set<Variable> addressedOfVariables);

	Set<Variable> writableVariables();

	/**
	 * This location or some location in the future contains dereferences of
	 * some pointers.
	 * 
	 * @return
	 */
	boolean hasDerefs();
}
