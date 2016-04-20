package edu.udel.cis.vsl.abc.front.IF;

import org.antlr.runtime.Token;

import edu.udel.cis.vsl.abc.err.IF.ABCException;

public class ParseException extends ABCException {

	/**
	 * Eclipse made me do it
	 */
	private static final long serialVersionUID = -5965287375421467649L;

	private Token token;

	public ParseException(String msg, Token token) {
		super("Parse error: " + token == null ? msg : msg + "\nAt " + token);
		this.token = token;
	}

	public ParseException(String msg) {
		super(msg);
	}

	public Token getToken() {
		return token;
	}
}
