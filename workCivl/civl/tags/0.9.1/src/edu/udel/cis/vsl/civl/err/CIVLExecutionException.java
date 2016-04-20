package edu.udel.cis.vsl.civl.err;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Sourceable;

public class CIVLExecutionException extends CIVLException {

	/**
	 * Added by Eclipse.
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * A certainty level gages how certain we are that this is error is a real
	 * error, i.e., not just a spurious error.
	 * 
	 * There are 3 levels, from highest to lowest level of certainty.
	 * 
	 * @author siegel
	 * 
	 */
	public enum Certainty {
		/**
		 * A concrete trace verifies this is an error: the highest level of
		 * certainty that this represents a real error in the program being
		 * analyzed.
		 */
		CONCRETE,
		/**
		 * A theorem prover says this is an error: second-highest level of
		 * certainty. However no conrete trace has been produced to verify the
		 * theorem prover's claim.
		 */
		PROVEABLE,
		/**
		 * The prover is not sure whether this is an error. It could be due to
		 * the incompleteness of the decision procecure, or it could be a real
		 * error.
		 */
		MAYBE,
		/**
		 * Probably an internal CIVL error: the theorem prover hasn't said
		 * anything. The lowest level of certaintly that this represents a real
		 * error in the program being analyzed.
		 */
		NONE
	}

	public enum ErrorKind {
		ARRAY_DECLARATION,
		ASSERTION_VIOLATION,
		COMMUNICATION,
		CYCLE,
		DEADLOCK,
		DEREFERENCE,
		DIVISION_BY_ZERO,
		FUNCTIONAL_COMPATIBILITY,
		INPUT_WRITE,
		INT_DIVISION,
		INTERNAL,
		INVALID_CAST,
		INVALID_PID,
		INVARIANT_VIOLATION,
		LIBRARY,
		MALLOC,
		MEMORY_LEAK,
		OTHER,
		OUT_OF_BOUNDS,
		OUTPUT_READ,
		POINTER,
		QUANTIFIER,
		SIZEOF,
		UNDEFINED_VALUE, UNION
	}

	private Certainty certainty;

	private ErrorKind kind;

	/**
	 * Constructs new CIVLException with given fields.
	 * 
	 * @param kind
	 *            the kind of error
	 * @param certainty
	 *            the certainty with which this is known to be an error in the
	 *            program being verified
	 * @param message
	 *            a message explaining the error
	 * @param source
	 *            the source code element associated to the error; may be null
	 */
	public CIVLExecutionException(ErrorKind kind, Certainty certainty,
			String message, CIVLSource source) {
		super(message, source);
		assert kind != null;
		assert certainty != null;
		this.kind = kind;
		this.certainty = certainty;
	}

	public CIVLExecutionException(ErrorKind kind, Certainty certainty,
			String message, Sourceable sourceable) {
		this(kind, certainty, message, sourceable.getSource());
	}

	public Certainty certainty() {
		return certainty;
	}

	public ErrorKind kind() {
		return kind;
	}

	@Override
	public String toString() {
		String result = "CIVL execution error (kind: " + kind + ", certainty: "
				+ certainty + ")\n";

		result += super.toString();
		return result;
	}
}
