package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

/**
 * This test class contains test methods for the pretty-printing of states.
 * 
 * @author Manchun Zheng
 *
 */
public class ShowStatesTest {
	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "showStates");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void structsArray() {
		assertTrue(ui.run("verify", "-showSavedStates",
				filename("structsArray.cvl")));
	}

	@Test
	public void symbolicArrayWrite() {
		assertTrue(ui.run("verify", "-showSavedStates",
				filename("symbolicArrayWrite.cvl")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
