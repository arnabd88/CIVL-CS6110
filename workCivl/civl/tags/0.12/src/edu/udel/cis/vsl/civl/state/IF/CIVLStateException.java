package edu.udel.cis.vsl.civl.state.IF;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.Certainty;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;

/**
 * Extends an execution exception with a state at which error occurred.
 * 
 * @author siegel
 * 
 */
public class CIVLStateException extends Exception {

	/**
	 * Eclipse generated.
	 */
	private static final long serialVersionUID = -6159425221287192305L;

	private State state;

	private ErrorKind kind;

	private Certainty certainty;

	private String message;

	private CIVLSource source;

	public CIVLStateException(ErrorKind kind, Certainty certainty,
			String message, State state, CIVLSource source) {
		this.kind = kind;
		this.certainty = certainty;
		this.message = message;
		assert state != null;
		this.state = state;
		this.source = source;
	}

	public CIVLSource source() {
		return this.source;
	}

	public State state() {
		return this.state;
	}

	public ErrorKind kind() {
		return this.kind;
	}

	public Certainty certainty() {
		return this.certainty;
	}

	public String message() {
		return this.message;
	}

	public String toString() {
		String result = super.toString() + "\n";
		ByteArrayOutputStream baos = new ByteArrayOutputStream();
		PrintStream ps = new PrintStream(baos);

		ps.print(state.toString());
		result += baos.toString();
		return result;
	}
}
