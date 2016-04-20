package edu.udel.cis.vsl.civl.kripke.IF;

import java.util.Map;
import java.util.Set;

import edu.udel.cis.vsl.civl.semantics.IF.Transition;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.civl.util.IF.Printable;
import edu.udel.cis.vsl.gmc.StateManagerIF;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * StateManager extends {@link StateManagerIF} for CIVL models.
 * 
 * @author Manchun Zheng
 * 
 */
public interface StateManager extends StateManagerIF<State, Transition> {

	/**
	 * Returns the number of objects of type State that have been instantiated
	 * since this JVM started.
	 * 
	 * @return the number of states instantiated
	 */
	long getNumStateInstances();

	/**
	 * Returns the number of states saved, i.e., made canonic.
	 * 
	 * @return the number of canonic states
	 */
	int getNumStatesSaved();

	/**
	 * @return The maximum number of processes in any state encountered by this
	 *         state manager.
	 */
	int maxProcs();

	/**
	 * Print an update message at your earliest possible convenience.
	 */
	void printUpdate();

	/**
	 * Set the field savedStates.
	 * 
	 * @param updater
	 *            The value to be used.
	 */
	void setUpdater(Printable updater);

	int numStatesExplored();

	/**
	 * Outputs collected for the model during the search.
	 * 
	 * @return
	 */
	Map<BooleanExpression, Set<Pair<State, SymbolicExpression[]>>> collectedOutputs();

	/**
	 * The names of output variables of the model.
	 * 
	 * @return
	 */
	String[] outptutNames();

}
