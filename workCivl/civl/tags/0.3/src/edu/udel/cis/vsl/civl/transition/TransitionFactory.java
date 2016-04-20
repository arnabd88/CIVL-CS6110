/**
 * 
 */
package edu.udel.cis.vsl.civl.transition;

import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.state.State;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * A factory to create transitions and transition sequences.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class TransitionFactory {

	/**
	 * A factory to create transitions and transition sequences.
	 */
	public TransitionFactory() {
	}

	/**
	 * Create a new simple transition.
	 * 
	 * @param pathCondition
	 *            The path condition that should be used when executing the
	 *            statement
	 * @param pid
	 *            The process id of the process executing this transition.
	 * @param statement
	 *            The statement corresponding to this transition.
	 * @return A new simple transition with the given path condition and
	 *         statement.
	 */
	public SimpleTransition newSimpleTransition(
			BooleanExpression pathCondition, int pid, Statement statement) {
		return new SimpleTransition(pathCondition, pid, statement);
	}

	/**
	 * Create a new choose transition.
	 * 
	 * @param pathCondition
	 *            The path condition that should be used when executing the
	 *            statement
	 * @param pid
	 *            The process id of the process executing this transition.
	 * @param statement
	 *            The statement corresponding to this transition.
	 * @param value
	 *            The value of returned by the choose for this transition.
	 * @return A new simple transition with the given path condition and
	 *         statement.
	 */
	public SimpleTransition newChooseTransition(
			BooleanExpression pathCondition, int pid, Statement statement,
			SymbolicExpression value) {
		return new ChooseTransition(pathCondition, pid, statement, value);
	}

	/**
	 * Create a new transition sequence.
	 * 
	 * @param state
	 *            The state of the program before this transition sequence
	 *            departs.
	 * @return A new transition sequence.
	 */
	public TransitionSequence newTransitionSequence(State state) {
		return new TransitionSequence(state);
	}

}
