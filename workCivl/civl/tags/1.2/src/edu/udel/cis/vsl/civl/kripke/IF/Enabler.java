package edu.udel.cis.vsl.civl.kripke.IF;

import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Transition;
import edu.udel.cis.vsl.civl.semantics.IF.TransitionSequence;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.gmc.EnablerIF;

/**
 * Enabler extends {@link EnablerIF} for CIVL models.
 * 
 * @author Manchun Zheng
 * 
 */
public interface Enabler extends
		EnablerIF<State, Transition, TransitionSequence> {

	/**
	 * Computes the guard of a statement. Since we have SystemGuardExpression
	 * and WaitGuardExpression, we don't need to compute the guard for system
	 * function calls and wait statements explicitly, which are now handled by
	 * the evaluator.
	 * 
	 * @param statement
	 *            The statement whose guard is to computed.
	 * @param pid
	 *            The ID of the process that the statement belongs to.
	 * @param state
	 *            The current state that the computation happens.
	 * @return The symbolic expression of the guard of the given statement.
	 */
	Evaluation getGuard(Statement statement, int pid, State state);
}
