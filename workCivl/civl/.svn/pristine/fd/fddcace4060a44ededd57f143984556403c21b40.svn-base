package edu.udel.cis.vsl.civl.log.IF;

import edu.udel.cis.vsl.civl.model.IF.CIVLException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.state.IF.State;

/**
 * This represents an error during the execution of a program.
 * 
 * @author Manchun Zheng
 *
 */
public class CIVLExecutionException extends CIVLException {

	/**
	 * Added by Eclipse.
	 */
	private static final long serialVersionUID = 1L;
	
	private State state = null;

	private Certainty certainty;

	private ErrorKind kind;

	private String process;

	private boolean reported = false;

	/**
	 * @param kind
	 *            the kind of error
	 * @param certainty
	 *            the certainty with which this is known to be an error in the
	 *            program being verified
	 * @param process
	 *            process name, i.e., "p"+process identifier
	 * @param message
	 *            a message explaining the error
	 * @param stateString
	 *            the string representation of the state where the error occurs;
	 *            may be null
	 * @param source
	 *            the source code element associated to the error; may be null
	 */
	public CIVLExecutionException(ErrorKind kind, Certainty certainty,
			String process, String message, State state, CIVLSource source) {
		super(message, source);
		assert kind != null;
		assert certainty != null;
		this.process = process;
		this.state = state;
		this.kind = kind;
		this.certainty = certainty;
	}

	/**
	 * @return the certainty of this error.
	 */
	public Certainty certainty() {
		return certainty;
	}

	/**
	 * @return the kind of this error.
	 */
	public ErrorKind kind() {
		return kind;
	}
	
	/**
	 * @return the state in which this error occurred.
	 */
	public State state() {
		return state;
	}

	/**
	 * Is this error reported?
	 * 
	 * @return true iff the error has already been reported
	 */
	public boolean isReported() {
		return this.reported;
	}

	/**
	 * Set this error to be reported.
	 */
	public void setReported() {
		this.reported = true;
	}

	@Override
	public String toString() {
		StringBuffer result = new StringBuffer();

		result.append("CIVL execution violation ");
		if (process != null) {
			result.append("in ");
			result.append(process);
			result.append(" ");
		}
		result.append("(kind: ");
		result.append(kind);
		result.append(", certainty: ");
		result.append(certainty);
		result.append(")");
		if (source != null) {
			result.append("\nat ");

			result.append(this.source.getSummary());
		}
		result.append(":\n");
		result.append(this.getMessage());
		if (this.state != null) {
			result.append("\n");
			result.append(this.state.callStackToString());
		}
		return result.toString();
	}
}
