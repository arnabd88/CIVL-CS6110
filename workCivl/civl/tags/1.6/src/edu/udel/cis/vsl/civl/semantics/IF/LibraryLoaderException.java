package edu.udel.cis.vsl.civl.semantics.IF;

/**
 * A library loader exception is produced by errors occur during when a library
 * executor/evaluator/enabler loader attempts to load a specific library
 * executor/evaluator/enabler.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class LibraryLoaderException extends Exception {
	
	/* *************************** Instance Fields ************************* */

	/**
	 * The error message from the library loader.
	 */
	private String message;

	/**
	 * Automatically generated code to get rid of warnings.
	 */
	private static final long serialVersionUID = -4619608037914000146L;

	/* ***************************** Constructors ************************** */

	/**
	 * Creates a new instance of library loader exception.
	 * 
	 * @param message
	 *            The error message of this exception.
	 */
	public LibraryLoaderException(String message) {
		this.message = message;
	}
	
	/* *********************** Methods from Exception ********************** */

	@Override
	public String getMessage() {
		return this.message;
	}
}
