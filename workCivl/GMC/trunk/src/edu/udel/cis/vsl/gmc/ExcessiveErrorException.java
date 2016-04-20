/**
 * 
 */
package edu.udel.cis.vsl.gmc;

/**
 * An exception thrown when the number of errors encountered in the course of a
 * search of a state-transition system exceeds some specified bound. Typical
 * applications will catch this exception and then truncate the search.
 * 
 * @author Stephen F. Siegel, University of Delaware
 */
public class ExcessiveErrorException extends RuntimeException {

	/** The number of errors encountered when this exception was thrown. */
	private int numErrors;

	/**
	 * Eclipse-generated id for serialization.
	 */
	private static final long serialVersionUID = 258799808968219986L;

	/**
	 * Constructs new instance with given numErrors.
	 * 
	 * @param numErrors
	 *            : the number of errors encountered when this exception was
	 *            thrown
	 */
	public ExcessiveErrorException(int numErrors) {
		super("The bound on the number of errors has been reached: "
				+ numErrors);
		this.numErrors = numErrors;
	}

	/**
	 * Returns the number of errors encountered when this exception was thrown
	 * 
	 * @return the number of errors encountered when this exception was thrown
	 */
	public int numErrors() {
		return numErrors;
	}
}
