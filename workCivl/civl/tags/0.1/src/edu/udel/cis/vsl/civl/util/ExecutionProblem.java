package edu.udel.cis.vsl.civl.util;

public class ExecutionProblem extends Exception {

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
		/* A concrete trace verifies this is an error */
		CONCRETE,
		/* The prover is not sure whether this is an error */
		MAYBE,
		/* Probably an internal TASS error */
		NONE,
		/* A theorem prover says this is an error */
		PROVEABLE
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
		UNDEFINED_VALUE
	}

	/**
	 * This is a compiler-generated serial id required to correctly implement
	 * Serializeable, inherited from Exception class.
	 */
	private static final long serialVersionUID = 6345634620954563631L;

	private Certainty certainty;

	private ErrorKind kind;

	public ExecutionProblem(ErrorKind kind, Certainty certainty, String message) {
		super(message);
		assert kind != null;
		assert certainty != null;
		assert message != null;
		this.kind = kind;
		this.certainty = certainty;
	}

	public Certainty certainty() {
		return certainty;
	}

	public ErrorKind kind() {
		return kind;
	}

	public String toString() {
		String result = "Execution error (kind: " + kind + ", certainty: "
				+ certainty + ")";

		result += "\n";
		result += getMessage();
		return result;
	}
}
