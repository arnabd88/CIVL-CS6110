package edu.udel.cis.vsl.civl;

import edu.udel.cis.vsl.civl.gui.IF.GUIs;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

/**
 * Main CIVL class, containing main method and a few static methods for running
 * CIVL.
 * 
 * @author Stephen F. Siegel, University of Delaware
 * 
 */
public class CIVL {

	/**
	 * Execute the appropriate CIVL tool(s) based on the command line arguments.
	 * 
	 * @param args
	 *            command line arguments; see {@link UserInterface}
	 */
	public static void main(String[] args) {
		if (args.length == 1 && "gui".equals(args[0])) {
			GUIs.startGUI();
		} else {
			UserInterface ui = new UserInterface();

			ui.run(args);
		}
	}

}
