package edu.udel.cis.vsl.civl.util;

/**
 * A CIVL internal exception represents an error that is
 * "not supposed to happen." It can be used like an assertion, whenever you feel
 * that something should always be true. It is a runtime exception, so there is
 * no need to declare or catch it. It will be thrown all the way up to main and
 * reported.
 */
public class CIVLInternalException extends RuntimeException {

	/**
	 * The generated serial ID to implement Serializaeable.
	 */
	private static final long serialVersionUID = 6522079858283496490L;

	public CIVLInternalException(String s) {
		super("A CIVL internal error has occurred.\n"
				+ "Please send an error report to siegel@udel.edu.\n" + s);
	}

}
