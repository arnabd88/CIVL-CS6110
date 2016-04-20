package edu.udel.cis.vsl.civl.semantics.IF;

import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;

/**
 * This represents a CIVL transition, which is deterministic and enabled at a
 * certain state. It is composed of a path condition, an atomic statement, a
 * PID, and a process identifier.
 * 
 * @author Manchun Zheng
 * 
 */
public interface Transition {

	public enum TransitionKind {
		NORMAL, NOOP
	}

	public enum AtomicLockAction {
		NONE, /** no action to the atomic lock */
		GRAB, /** attempts to grab the atomic lock */
		RELEASE
		/** releases the atomic lock */
	}

	/**
	 * The path condition of the new state after this transition is executed.
	 * 
	 * @return The path condition of the new state after this transition is
	 *         executed.
	 */
	BooleanExpression pathCondition();

	/**
	 * The statement that this transition is to execute, which should be atomic,
	 * deterministic, and enabled in the context of the path condition.
	 * 
	 * @return The statement that this transition is to execute
	 */
	Statement statement();

	/**
	 * The PID of the process that this transition belongs to.
	 * 
	 * @return The PID of the process that this transition belongs to.
	 */
	int pid();

	/**
	 * The identifier of the process that this transition belongs to.
	 * 
	 * @return The identifier of the process that this transition belongs to.
	 */
	int processIdentifier();

	/**
	 * The atomic lock action associates with this transition. See
	 * {@link AtomicLockAction} for more details.
	 * 
	 * @return the atomic lock action associates with this transition.
	 */
	AtomicLockAction atomicLockAction();

	/**
	 * returns the kind of this transition.
	 * 
	 * @return
	 */
	TransitionKind transitionKind();

	/**
	 * Shall the state be simplified after the transition is done?
	 * 
	 * @return
	 */
	boolean simpifyState();
}
