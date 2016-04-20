package edu.udel.cis.vsl.civl.library.IF;

import edu.udel.cis.vsl.civl.err.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.library.CommonLibraryLoader;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.state.IF.State;

/**
 * A Library Executor provides the semantics for system functions defined in a
 * library. It provides a method to "execute" each system library function.A new
 * library is implemented in the package named as
 * "edu.udel.cis.vsl.civl.library." ( {@link CommonLibraryLoader#CLASS_PREFIX})
 * + library name. And the class name of the executor is: "Lib" + library name +
 * "Enabler". For example, the stdio library executor is implemented as the
 * class edu.udel.cis.vsl.civl.library.stdio.LibstdioExecutor.
 * 
 */
public interface LibraryExecutor {

	/**
	 * Returns the state that results from executing the statement, or null if
	 * path condition becomes unsatisfiable.
	 */
	State execute(State state, int pid, CallOrSpawnStatement statement)
			throws UnsatisfiablePathConditionException;

	// TODO: Is this ever being done?
	/**
	 * Initializes the part of the state dealing with the library.
	 */
	State initialize(State state);

	/**
	 * A method invoked at any terminal state. The library performs any final
	 * actions before system shutdown and may also check certain properties hold
	 * and throw an exception or log errors if they do not. For example, the MPI
	 * library may check there are no unreceived messages. The stdio library may
	 * check there are no open streams.
	 */
	State wrapUp(State state);

}
