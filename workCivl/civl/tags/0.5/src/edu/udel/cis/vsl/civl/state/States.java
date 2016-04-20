package edu.udel.cis.vsl.civl.state;

import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.state.immutable.ImmutableStateFactory;
import edu.udel.cis.vsl.civl.state.persistent.PersistentStateFactory;
import edu.udel.cis.vsl.civl.state.trans.TransientStateFactory;

/**
 * Entry point for the state module: provides a static method to get a new state
 * factory. The usual way to get a state factory is to first create a
 * modelFactory and then invoke
 * <code>States.newStateFactory(modelFactory)</code>.
 * 
 * @author siegel
 * 
 */
public class States {

	/**
	 * Returns a new immutable state factory based on the given model factory.
	 * This implementation of StateFactory uses the Immutable Pattern: all
	 * states (and components) are immutable.
	 * 
	 * @param modelFactory
	 *            a model factory
	 * @return a new immutable state factory
	 */
	public static StateFactory newImmutableStateFactory(
			ModelFactory modelFactory) {
		return new ImmutableStateFactory(modelFactory);
	}

	public static StateFactory newPersistentStateFactory(
			ModelFactory modelFactory) {
		return new PersistentStateFactory(modelFactory);
	}

	/**
	 * Returns a new transient state factory based on the given model factory.
	 * This implementation of StateFactory uses the Transient Pattern: states
	 * (and their components) begin in a mutable state and become immutable
	 * (mostly) once they are "committed".
	 * 
	 * @param modelFactory
	 *            a model factory
	 * @return a new transient state factory
	 */
	public static StateFactory newTransientStateFactory(
			ModelFactory modelFactory) {
		return new TransientStateFactory(modelFactory);
	}

}
