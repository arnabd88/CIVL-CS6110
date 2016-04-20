package edu.udel.cis.vsl.civl;

import edu.udel.cis.vsl.abc.ABC;
import edu.udel.cis.vsl.abc.ABC.Language;
import edu.udel.cis.vsl.civl.run.UserInterface;

/**
 * Main CIVL class, containing main method and a few static methods for running
 * CIVL.
 * 
 * @author Stephen F. Siegel, University of Delaware
 * 
 */
public class CIVL {

	/** Sets the front-end language to CIVL_C, not C. */
	static {
		ABC.language = Language.CIVL_C;
	}

	/** The version of this release of CIVL. */
	public final static String version = "0.11";

	/**
	 * The date of this release of CIVL. Format: YYYY-MM-DD in accordance with
	 * ISO 8601.
	 */
	public final static String date = "2014-04-22";

	/**
	 * Execute the appropriate CIVL tool(s) based on the command line arguments.
	 * 
	 * @param args
	 *            command line arguments; see {@link UserInterface}
	 */
	public static void main(String[] args) {
		UserInterface ui = new UserInterface();

		ui.run(args);
	}

}
