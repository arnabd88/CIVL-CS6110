package edu.udel.cis.vsl.civl;

import edu.udel.cis.vsl.civl.gui.IF.GUIs;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

/**
 * The main CIVL class, containing the main method, which provides the command
 * line interface for using CIVL.
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
			if (args.length < 1 || !args[0].equals("replay"))
				System.exit(0);
		}
	}

}
