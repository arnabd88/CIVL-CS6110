package edu.udel.cis.vsl.civl.model.IF;

import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.civl.model.common.ABC_CIVLSource;

/**
 * A CIVL internal exception represents an error that is
 * "not supposed to happen." It can be used like an assertion, whenever you feel
 * that something should always be true. It is a runtime exception, so there is
 * no need to declare or catch it. It will be thrown all the way up to main and
 * reported.
 */
public class CIVLInternalException extends CIVLException {

	/**
	 * The generated serial ID to implement Serializaeable.
	 */
	private static final long serialVersionUID = 6522079858283496490L;

	public CIVLInternalException(String s, CIVLSource source) {
		super("A CIVL internal error has occurred."
				+ " Please report the error to civl-dev@googlegroups.com.\n"
				+ s, source);
	}

	public CIVLInternalException(String s, Sourceable sourceable) {
		this(s, sourceable.getSource());
	}

	public CIVLInternalException(String s, Source source) {
		this(s, new ABC_CIVLSource(source));
	}
}
