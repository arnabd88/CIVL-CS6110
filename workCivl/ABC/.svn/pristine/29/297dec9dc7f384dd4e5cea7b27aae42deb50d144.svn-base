package edu.udel.cis.vsl.abc.err.IF;

/**
 * An error which is thrown when there is feature that has not yet been
 * implemented in ABC. The string "ABC does not yet support " will be prepended
 * to the message. This is a runtime exception.
 * 
 * @author siegel
 *
 */
public class ABCUnsupportedException extends ABCRuntimeException {

	/**
	 * Generated ID for serialization.
	 */
	private static final long serialVersionUID = -7451309960801544746L;

	public ABCUnsupportedException(String unsupportedFeature) {
		super("ABC does not yet support " + unsupportedFeature);
	}

	public ABCUnsupportedException(String unsupportedFeature, String location) {
		super("ABC does not yet support " + unsupportedFeature, location);
	}

}
