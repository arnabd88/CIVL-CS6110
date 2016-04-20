package edu.udel.cis.vsl.civl.semantics.IF;

import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;

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
	 * <p>
	 * Executes the given call statement for a certain process at the given
	 * state.
	 * </p>
	 * <p>
	 * Precondition: the given call statement is enabled for the process with
	 * the given pid, and the function of the call statement is provided by this
	 * library.
	 * </p>
	 * 
	 * @param state
	 *            The state where the call statement is to be executed.
	 * @param pid
	 *            The PID of the process that the statement belongs to.
	 * @param statement
	 *            The call statement to be executed.
	 * @return The resulting state after executing the call statement.
	 * @throws UnsatisfiablePathConditionException
	 */
	State execute(State state, int pid, CallOrSpawnStatement statement)
			throws UnsatisfiablePathConditionException;
}
