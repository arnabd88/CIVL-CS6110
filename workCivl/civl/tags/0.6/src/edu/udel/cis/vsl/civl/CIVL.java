package edu.udel.cis.vsl.civl;

import java.io.File;
import java.io.PrintStream;

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
	public final static String version = "0.6";

	/**
	 * The date of this release of CIVL. Format: YYYY-MM-DD in accordance with
	 * ISO 8601.
	 */
	public final static String date = "2014-02-01";

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

	public static boolean verify(File file, PrintStream out) {
		return verify(false, false, file, out, false);
	}

	public static boolean verify(boolean printModel, boolean verbose,
			File file, PrintStream out) {
		return verify(printModel, verbose, file, out, false);
	}

	public static boolean verify(boolean printModel, boolean verbose,
			File file, PrintStream out, boolean randomMode) {
		UserInterface ui = new UserInterface();

		String[] args = new String[] { "verify", "-showModel=" + printModel,
				"-verbose=" + verbose, "-random=" + randomMode, file.getPath() };

		return ui.run(args);
	}
}
