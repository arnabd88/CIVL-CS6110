package edu.udel.cis.vsl.abc.token.IF;

import edu.udel.cis.vsl.abc.err.IF.ABCException;

/**
 * An exception for which the source (in the source program being compiled) is
 * unknown. The expectation is that this exception will be caught internally by
 * a method lower on the call stack which does know the source, and that method
 * will construct a SyntaxException from this exception, specifying the source.
 * 
 * @author siegel
 * 
 */
public class UnsourcedException extends ABCException {

	/**
	 * Eclipse made me do it
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * Constructs a new unsourced exception wrapping the given message
	 * 
	 * @param message
	 *            a message which will be incorporated into the final message
	 *            printed to the user
	 */
	public UnsourcedException(String message) {
		super(message);
	}

}
