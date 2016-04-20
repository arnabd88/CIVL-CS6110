package edu.udel.cis.vsl.civl.model.IF;

import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.civl.model.common.ABC_CIVLSource;

/**
 * An exception thrown when there is syntax error in the program being verified,
 * e.g., calling $choose_int with more than one arguments, executing $wait in
 * $atom block, etc.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class CIVLSyntaxException extends CIVLException {

	/**
	 * Generated ID.
	 */
	private static final long serialVersionUID = -7304144606936703023L;

	public CIVLSyntaxException(String message, CIVLSource source) {
		super("Syntax error: " + message, source);
	}

	public CIVLSyntaxException(String message, Sourceable sourceable) {
		super("Syntax error: " + message, sourceable.getSource());
	}

	public CIVLSyntaxException(String message) {
		super("Syntax error: " + message, (CIVLSource) null);
	}

	public CIVLSyntaxException(String message, Source source) {
		this(message, new ABC_CIVLSource(source));
	}
}
