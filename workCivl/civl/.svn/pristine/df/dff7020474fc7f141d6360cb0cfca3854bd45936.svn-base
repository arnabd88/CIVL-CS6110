package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class ReasoningTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "reasoning");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods *************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void neqZero() throws ABCException {
		assertTrue(ui.run("verify", filename("neqZero.cvl")));
	}

	@Test
	public void evaluatePc() throws ABCException {
		assertFalse(ui.run("verify", filename("evaluatePc.cvl")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
