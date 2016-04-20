package edu.udel.cis.vsl.abc.token.IF;

/**
 * An Inclusion represents the application of a preprocessor
 * <code>#include</code> directive.
 * 
 * @author siegel
 * 
 */
public interface Inclusion extends Formation {

	/**
	 * Returns the file which was <code>#include</code>-d.
	 * 
	 * @return the included file
	 */
	SourceFile getFile();

	/**
	 * Returns the token containing the file name in the include directive. The
	 * token text will have the form <code><foo.c></code> or
	 * <code>"foo.c"</code>. You can get the line number and so on from this
	 * token.
	 * 
	 * @return the token containing the file name from the include directive
	 */
	CivlcToken getIncludeToken();

}
