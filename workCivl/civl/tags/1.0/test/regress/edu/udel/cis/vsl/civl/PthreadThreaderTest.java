package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class PthreadThreaderTest {
	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File(new File("examples"),
			"pthread"), "threader");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods *************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void dekker_true() throws ABCException {
		assertTrue(ui.run("verify", "-svcomp", filename("dekker_true.c")));
	}

	@Test
	public void lamport_true() throws ABCException {
		assertTrue(ui.run("verify", "-svcomp", filename("lamport_true.c")));
	}

	@Test
	public void peterson_true() throws ABCException {
		assertTrue(ui.run("verify", "-svcomp", filename("peterson_true.c")));
	}

	@Test
	public void qrcu_false() throws ABCException {
		assertFalse(ui.run("verify", "-svcomp", filename("qrcu_false.c")));
	}

	@Test
	public void read_write_lock_false() throws ABCException {
		assertFalse(ui.run("verify", "-svcomp",
				filename("read_write_lock_false.c")));
	}

	@Test
	public void read_write_lock_true() throws ABCException {
		assertTrue(ui.run("verify", "-svcomp",
				filename("read_write_lock_true.c")));
	}

	@Test
	public void szymanski_true() throws ABCException {
		assertTrue(ui.run("verify", "-svcomp", filename("szymanski_true.c")));
	}

	@Test
	public void time_var_mutex_true() throws ABCException {
		assertTrue(ui.run("verify", "-svcomp",
				filename("time_var_mutex_true.c")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
