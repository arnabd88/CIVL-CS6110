package edu.udel.cis.vsl.civl.util.IF;

import java.io.PrintStream;

/**
 * An object supporting a "print" method.
 * 
 * @author siegel
 * 
 */
public interface Printable {

	/**
	 * Print something to the given output stream. Will not necessarily flush
	 * the stream.
	 * 
	 * @param out
	 *            the stream to which the output will be printed
	 */
	void print(PrintStream out);

}
