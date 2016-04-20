package edu.udel.cis.vsl.civl.kripke.IF;

import edu.udel.cis.vsl.civl.semantics.IF.Transition;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.gmc.TraceStepIF;

/**
 * 
 * TraceStep extends {@link TraceStepIF} for CIVL models. A CIVL trace step is
 * composed of a sequence of atomic steps executed by a single process.
 * 
 * @see AtomicStep
 * 
 * @author Manchun Zheng
 * 
 */
public interface TraceStep extends TraceStepIF<Transition, State> {

	/**
	 * Adds an atomic step to the trace step.
	 * 
	 * @param step
	 *            The atomic step to be added.
	 */
	void addAtomicStep(AtomicStep step);

	/**
	 * Returns the number of atomic steps contained in this trace step.
	 * 
	 * @return the number of atomic steps contained in this trace step.
	 */
	int getNumAtomicSteps();

	/**
	 * Returns the identifier of the process that this trace step belongs to.
	 * 
	 * @return the identifier of the process that this trace step belongs to.
	 */
	int processIdentifier();

	/**
	 * Returns the list of atomic steps of this trace step.
	 * 
	 * @return the list of atomic steps of this trace step.
	 */
	Iterable<AtomicStep> getAtomicSteps();

	/**
	 * <p>
	 * Completes the trace step with its final state.
	 * </p>
	 * 
	 * <p>
	 * Precondition:<code> this.getFinalState() == null</code>, otherwise, an
	 * exception will be thrown.
	 * </p>
	 * 
	 * @param finalState
	 *            The state to be used as the final state of the trace step.
	 */
	void complete(State finalState);

	/**
	 * Returns the final state of this trace step.
	 * 
	 * @return the final state of this trace step.
	 */
	State getFinalState();
}
