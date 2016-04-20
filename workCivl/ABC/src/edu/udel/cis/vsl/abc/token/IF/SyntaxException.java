package edu.udel.cis.vsl.abc.token.IF;

import edu.udel.cis.vsl.abc.err.IF.ABCException;

public class SyntaxException extends ABCException {

	/**
	 * Eclipse made me do it.
	 */
	private static final long serialVersionUID = -2355680870938982989L;

	private Source source;

	public SyntaxException(String message, Source source) {
		super(message, source.getSummary(false));
		this.source = source;
	}

	public SyntaxException(UnsourcedException oldException, Source newSource) {
		this(oldException.getMessage(), newSource);
	}

	public Source getSource() {
		return source;
	}

}
