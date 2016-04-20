package edu.udel.cis.vsl.abc.front.IF;

import org.antlr.runtime.Token;


/**
 * An exception that is thrown when there is a problem evaluating a preprocessor
 * expression. A preprocessor expression occurs in a "#if" conditional
 * directive.
 * 
 * @author siegel
 * 
 */
public class PreprocessorExpressionException extends PreprocessorException {

	/**
	 * Eclipse made me do it.
	 */
	private static final long serialVersionUID = 1L;

	public PreprocessorExpressionException(String msg) {
		super(msg);
	}

	public PreprocessorExpressionException(String msg, Token token) {
		super(msg, token);
	}

}
