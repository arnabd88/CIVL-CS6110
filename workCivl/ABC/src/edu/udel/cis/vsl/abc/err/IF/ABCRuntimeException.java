package edu.udel.cis.vsl.abc.err.IF;

/**
 * The root of the ABC runtime exception hierarchy. These are exceptions that do
 * not have to be declared or caught.
 * 
 * @author siegel
 * 
 */
public class ABCRuntimeException extends RuntimeException {

	private String location;

	/**
	 * Generated ID for serialization.
	 */
	private static final long serialVersionUID = 2113037197514976162L;

	public ABCRuntimeException(String message) {
		super(message);
	}

	public ABCRuntimeException(String message, String location) {
		super(message);
		this.location = location;
	}

	public String toString() {
		String result = "Error: " + getMessage();

		if (location != null)
			result += "\nat " + location;
		return result;
	}

}
