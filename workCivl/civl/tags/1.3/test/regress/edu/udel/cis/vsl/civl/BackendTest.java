package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class BackendTest {
	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "backend");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */
	@Test
	public void printExpr() {
		assertTrue(ui
				.run("verify -showProgram=false -showSavedStates -showTransitions",
						filename("printExpr.cvl")));
	}
	
	@Test
	public void arrayWrite() {
		assertTrue(ui
				.run("verify -showProgram=false -showSavedStates -showTransitions",
						filename("arrayWrite.cvl")));
	}

	@Test
	public void showTrans() {
		assertTrue(ui.run("verify -showProgram -showTransitions",
				filename("showTrans.cvl")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
