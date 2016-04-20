package edu.udel.cis.vsl.gmc;

import java.util.ArrayList;
import java.util.List;

/**
 * This represents a trace of an execution of a given model.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 * @param <TRANSITION>
 *            the type used to represent transitions in the state-transition
 *            system being analyzed
 * @param <STATE>
 *            the type used to represent states in the state-transition system
 *            being analyzed
 */
public class Trace<TRANSITION, STATE> {
	/**
	 * The initial state of the trace.
	 */
	private STATE init;

	/**
	 * The list of trace steps contained by the trace.
	 */
	private List<TraceStepIF<TRANSITION, STATE>> traceSteps;

	/**
	 * The name of the trace.
	 */
	private String name;

	/**
	 * The flag denoting if any violations have been encountered in the trace.
	 */
	private boolean violation;

	/* ***************************** Constructors ************************** */

	/**
	 * Creates a new instance of Trace.
	 * 
	 * @param name
	 *            The name of the new trace.
	 * @param init
	 *            The initial state of the new trace.
	 */
	public Trace(String name, STATE init) {
		this.init = init;
		this.name = name;
		this.traceSteps = new ArrayList<>();
		violation = false;
	}

	/* ************************* Methods from Object *********************** */

	@Override
	public String toString() {
		StringBuffer result = new StringBuffer();

		result.append(init);
		for (TraceStepIF<TRANSITION, STATE> traceStep : traceSteps) {
			result.append("\n");
			result.append(traceStep);
		}
		return result.toString();
	}

	/* ************************* Other Public Methods ********************** */

	/**
	 * Returns the initial state of this trace.
	 * 
	 * @return the initial state of this trace.
	 */
	public STATE init() {
		return this.init;
	}

	/**
	 * Returns the name of this trace.
	 * 
	 * @return the name of this trace.
	 */
	public String name() {
		return name;
	}

	/**
	 * Returns the verification result of this trace.
	 * 
	 * @return the verification result of this trace.
	 */
	public boolean result() {
		return !this.violation;
	}

	/**
	 * Returns true iff a least one violations have been encountered.
	 * 
	 * @return true iff a least one violations have been encountered.
	 */
	public boolean violation() {
		return this.violation;
	}

	/**
	 * Updates the flag of violation.
	 * 
	 * @param val
	 *            The value to use as the flag of violation.
	 */
	public void setViolation(boolean val) {
		this.violation = val;
	}

	/**
	 * Returns the last state of this trace.
	 * 
	 * @return the last state of this trace.
	 */
	public STATE lastState() {
		int size = traceSteps.size();

		if (size < 1)
			return this.init;
		return this.traceSteps.get(size - 1).getFinalState();
	}

	/**
	 * Adds a new trace step to this trace.
	 * 
	 * @param traceStep
	 *            The new trace step to be added.
	 */
	public void addTraceStep(TraceStepIF<TRANSITION, STATE> traceStep) {
		this.traceSteps.add(traceStep);
	}

	/**
	 * Returns the list of trace steps contained in this trace.
	 * 
	 * @return the list of trace steps contained in this trace.
	 */
	public List<TraceStepIF<TRANSITION, STATE>> traceSteps() {
		return this.traceSteps;
	}

	/**
	 * Returns the i'th trace step of this trace.
	 * 
	 * @param i
	 *            The index of the trace step to be returned.
	 * @return the i'th trace step of this trace.
	 */
	public TraceStepIF<TRANSITION, STATE> traceStep(int i) {
		return this.traceSteps.get(i);
	}

	/**
	 * Returns the number of trace steps in this trace.
	 * 
	 * @return the number of trace steps in this trace.
	 */
	public int numOfSteps() {
		return this.traceSteps.size();
	}

}
