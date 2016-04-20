package edu.udel.cis.vsl.civl.model.IF;

import java.io.PrintStream;

/**
 * A CIVLSource object represents a range of text in a source file.
 * 
 * @author siegel
 * 
 */
public interface CIVLSource {

	/**
	 * Returns a human-readable string representation of this range of source
	 * data.
	 * 
	 * @return user-friendly readable representation
	 */
	String toString();

	/**
	 * Prints the source to print stream.
	 * 
	 * @param out
	 *            a PrintStream
	 */
	void print(PrintStream out);

	/**
	 * Returns location information only (not actual source text). For example
	 * "foo.c:127.4-128.1".
	 * 
	 */
	String getLocation();

	/**
	 * Returns summary of location and text.
	 * 
	 * @return
	 */
	String getSummary();

	void printShorterFileNameMap(PrintStream out);
}
