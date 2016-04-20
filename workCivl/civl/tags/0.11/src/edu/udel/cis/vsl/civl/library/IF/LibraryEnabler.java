package edu.udel.cis.vsl.civl.library.IF;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.udel.cis.vsl.civl.library.CommonLibraryLoader;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.semantics.Evaluation;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.transition.SimpleTransition;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * A Library Enabler provides computes the enabled transitions of system
 * function calls at certain states. It also provides a method to "evaluate" the
 * guard of each system function call. A new library is implemented in the
 * package named as "edu.udel.cis.vsl.civl.library." (
 * {@link CommonLibraryLoader#CLASS_PREFIX}) + library name. And the class name
 * of the enabler is: "Lib" + library name + "Enabler". For example, the stdio
 * library enabler is implemented as the class
 * edu.udel.cis.vsl.civl.library.stdio.LibstdioEnabler.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public interface LibraryEnabler {
	/**
	 * Gets a guard for a system function. This is an extra guard relating to
	 * the particular system function, and needs to be checked in addition to
	 * the "regular" guard in the transition system.
	 */
	Evaluation evaluateGuard(CIVLSource source, State state, int pid,
			String function, List<Expression> arguments);

	/**
	 * Computes the ample set process ID's from a system function call.
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the process that the system function call belongs
	 *            to.
	 * @param statement
	 *            The system function call statement.
	 * @param reachableMemUnitsMap
	 *            The map of reachable memory units of all active processes.
	 * @return
	 */
	Set<Integer> ampleSet(State state, int pid, CallOrSpawnStatement statement,
			Map<Integer, Map<SymbolicExpression, Boolean>> reachableMemUnitsMap);

	/**
	 * Computes the enabled transitions of a given function call. This is to
	 * support nondeterministic function calls.
	 * 
	 * @param state
	 *            The current state.
	 * @param call
	 *            The function call statement, upon which the set of enabled
	 *            transitions will be computed.
	 * @param pathCondition
	 *            The current path condition.
	 * @param pid
	 *            The ID of the process that the function call belongs to.
	 * @param assignAtomicLock
	 *            The assignment statement for the atomic lock variable, should
	 *            be null except that the process is going to re-obtain the
	 *            atomic lock variable.
	 * @return The set of enabled transitions.
	 */
	ArrayList<SimpleTransition> enabledTransitions(State state,
			CallOrSpawnStatement call, BooleanExpression pathCondition,
			int pid, int processIdentifier, Statement assignAtomicLock);
}
