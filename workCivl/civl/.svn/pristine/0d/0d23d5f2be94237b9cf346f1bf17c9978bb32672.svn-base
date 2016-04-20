package edu.udel.cis.vsl.civl.err;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;

/**
 * Extends an execution exception with a state at which error occurred.
 * 
 * @author siegel
 * 
 */
public class CIVLStateException extends CIVLExecutionException {

	/**
	 * Eclipse generated.
	 */
	private static final long serialVersionUID = -6159425221287192305L;

	/**
	 * State at which error occurred
	 */
	private State state;

	private StateFactory stateFactory;

	public CIVLStateException(ErrorKind kind, Certainty certainty,
			String message, State state, StateFactory stateFactory,
			CIVLSource source) {
		super(kind, certainty, message, source);
		assert state != null;
		this.state = state;
		this.stateFactory = stateFactory;
	}

	public String toString() {
		String result = super.toString() + "\n";
		ByteArrayOutputStream baos = new ByteArrayOutputStream();
		PrintStream ps = new PrintStream(baos);

		this.stateFactory.printState(ps, state);
		// state.print(ps);
		result += baos.toString();
		return result;
	}

	State getState() {
		return state;
	}

}
