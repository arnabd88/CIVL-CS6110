/**
 * 
 */
package edu.udel.cis.vsl.civl.log;

/**
 * @author zirkel
 *
 */
public class ExcessiveErrorException extends RuntimeException {

	private int numErrors;
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 258799808968219986L;

	/**
	 * 
	 */
	public ExcessiveErrorException(int numErrors) {
		super("The bound on the number of errors has been reached.");
		this.numErrors = numErrors;
	}

	public int numErrors() {
		return numErrors;
	}
}
