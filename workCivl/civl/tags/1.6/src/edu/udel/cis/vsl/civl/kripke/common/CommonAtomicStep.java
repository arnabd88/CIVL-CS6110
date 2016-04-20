package edu.udel.cis.vsl.civl.kripke.common;

import edu.udel.cis.vsl.civl.kripke.IF.AtomicStep;
import edu.udel.cis.vsl.civl.model.IF.location.Location.AtomicKind;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.semantics.IF.Transition;
import edu.udel.cis.vsl.civl.state.IF.State;

/**
 * This represents an atomic execution step, which represents the execution of
 * exactly one (deterministic) transition. This class includes a reference to
 * the post-state but not to the pre-state. Typically, an atomic step appears in
 * a trace step, and the post-state of the previous atomic step is the
 * pre-state.
 * 
 * @author Manchun Zheng
 * 
 */
public class CommonAtomicStep implements AtomicStep {

	/* *************************** Instance Fields ************************* */

	/**
	 * The state after executing the transition from a certain state.
	 */
	private State postState;

	/**
	 * The transition executed during this step
	 */
	private Transition transition;

	/* ***************************** Constructors ************************** */

	/**
	 * <p>
	 * Creates a new instance of an atomic step.
	 * </p>
	 * <p>
	 * Precondition: there exists a state in the state space such that executing
	 * <code>transition</code> from that state resulting in <code>target</code>
	 * state.
	 * </p>
	 * 
	 * @param postState
	 * @param transition
	 */
	public CommonAtomicStep(State postState, Transition transition) {
		this.postState = postState;
		this.transition = transition;
	}

	/* ************************* Methods from Object *********************** */

	@Override
	public String toString() {
		StringBuffer result = new StringBuffer();

		result.append(" - ");
		result.append(transition.statement().toStepString(AtomicKind.NONE,
				transition.pid(), false));
		result.append(" -> ");
		result.append(this.postState.toString());
		return result.toString();
	}

	/* *********************** Methods from AtomicStep ********************* */

	@Override
	public void setPostState(State state) {
		this.postState = state;
	}

	@Override
	public State getPostState() {
		return this.postState;
	}

	@Override
	public Statement getStatement() {
		return transition.statement();
	}
}
