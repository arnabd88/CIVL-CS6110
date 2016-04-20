package edu.udel.cis.vsl.civl.semantics.IF;

import java.util.List;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;

/**
 * A Library Evaluator provides a method to "evaluate" the guard of each system
 * function call. A new library is implemented in the package named as
 * "edu.udel.cis.vsl.civl.library." ( {@link CommonLibraryLoader#CLASS_PREFIX})
 * + library name. And the class name of the enabler is: "Lib" + library name +
 * "Evaluator". For example, the stdio library enabler is implemented as the
 * class edu.udel.cis.vsl.civl.library.stdio.LibstdioEnabler.
 * 
 * @author zmanchun
 * 
 */
public interface LibraryEvaluator {

	/**
	 * Evaluates the guard of a system function. This is an extra guard related
	 * to the particular system function, and needs to be checked in addition to
	 * the "regular" guard in the transition system.
	 * 
	 * @param source
	 *            The source code information for error report.
	 * @param state
	 *            The state where the evaluation happens.
	 * @param pid
	 *            The PID of the process that triggers this evaluation.
	 * @param function
	 *            The name of the function.
	 * @param arguments
	 *            The arguments of the function.
	 * @return The result of the guard with a possibly new state caused by side
	 *         effects.
	 * @throws UnsatisfiablePathConditionException
	 */
	Evaluation evaluateGuard(CIVLSource source, State state, int pid,
			String function, List<Expression> arguments)
			throws UnsatisfiablePathConditionException;

}
