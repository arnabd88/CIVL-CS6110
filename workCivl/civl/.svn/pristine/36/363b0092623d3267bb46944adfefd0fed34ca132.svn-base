package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class SpecialStatementsTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"),
			"specialStatements");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods *************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void choose1() throws ABCException {
		assertTrue(ui.run("verify", filename("choose1.cvl")));
	}

	@Test
	public void choose_bad1() throws ABCException {
		assertFalse(ui.run("show", filename("choose_bad1.cvl")));
	}

	@Test
	public void choose_bad2() throws ABCException {
		assertFalse(ui.run("show", filename("choose_bad2.cvl")));
	}

	@Test
	public void choose_bad3() throws ABCException {
		assertFalse(ui.run("show", filename("choose_bad3.cvl")));
	}

	@Test
	public void when1() throws ABCException {
		assertTrue(ui.run("verify", filename("when1.cvl")));
	}

	@Test
	public void when2() throws ABCException {
		assertTrue(ui.run("verify", filename("when2.cvl")));
	}

	@Test
	public void when3() throws ABCException {
		assertTrue(ui.run("verify", filename("when3.cvl")));
	}
}
