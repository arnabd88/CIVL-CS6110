package edu.udel.cis.vsl.civl.model.IF;

/**
 * A system function is a function that is implemented in a library executor,
 * not in source code.
 * 
 * @author zirkel
 * 
 */
public interface SystemFunction extends Function {

	/**
	 * 
	 * @return The name of the library containing this system function.
	 */
	public String getLibrary();

	/**
	 * 
	 * @param libraryName
	 *            The name of the library containing this system function.
	 */
	public void setLibrary(String libraryName);

}
