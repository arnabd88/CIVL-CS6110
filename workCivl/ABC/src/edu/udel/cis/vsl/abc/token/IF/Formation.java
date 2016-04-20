package edu.udel.cis.vsl.abc.token.IF;

/**
 * A formation is a record of the history of events that went into the formation
 * of a token. Examples of such events include preprocessor inclusion (
 * <code>#include</code>), preprocessor macro expansion, and adjacent string
 * literal concatenation.
 * 
 * Formations may have a recursive structure.
 * 
 * @author siegel
 * 
 */
public interface Formation {

	/**
	 * Returns a human-readable textual description of this formation that is
	 * not a complete sentence, but is meant to be appended to a string that
	 * describes the token. For example, this method might returns something
	 * like "formed by concatenating ...".
	 * 
	 * @return desription of formation as clause to be appended to description
	 *         of token
	 */
	String suffix();

	/**
	 * In the sequence of files that led, through inclusion, to the creation of
	 * the token, this returns the last file. Hence it is the file that is
	 * closest to the final token.
	 * 
	 * @return last file in inclusion sequence
	 */
	SourceFile getLastFile();
}
