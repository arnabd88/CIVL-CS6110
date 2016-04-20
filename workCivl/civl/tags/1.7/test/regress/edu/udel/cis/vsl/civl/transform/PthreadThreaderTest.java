package edu.udel.cis.vsl.civl.transform;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.civl.TestConstants;
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
		assertTrue(ui.run("verify", "-svcomp16 -showProgram=false",
				TestConstants.QUIET, filename("dekker_true-unreach-call.c")));
	}

	@Test
	public void lamport_true() throws ABCException {
		assertTrue(ui.run("verify", "-svcomp16", TestConstants.QUIET,
				filename("lamport_true-unreach-call.c")));
	}

	@Test
	public void peterson_true() throws ABCException {
		assertTrue(ui.run("verify", "-svcomp16", TestConstants.QUIET,
				filename("peterson_true-unreach-call.c")));
	}

	@Test
	public void qrcu_false() throws ABCException {
		assertFalse(ui.run("verify", "-svcomp16", TestConstants.QUIET,
				filename("qrcu_false-unreach-call.c")));
	}

	@Test
	public void read_write_lock_false() throws ABCException {
		assertFalse(ui.run("verify", "-svcomp16", TestConstants.QUIET,
				filename("read_write_lock_false-unreach-call.c")));
	}

	@Test
	public void read_write_lock_true() throws ABCException {
		// assertTrue(ui.run("verify", "-svcomp16 -showProgram",
		// filename("read_write_lock_true-unreach-call.c")));
		assertTrue(ui.run("verify", "-svcomp16 -showProgram=false",
				TestConstants.QUIET,
				filename("read_write_lock_true-unreach-call.c")));
		// ui.run("replay", "-svcomp16 -showTransitions",
		// filename("read_write_lock_true-unreach-call.c"));
	}

	@Test
	public void szymanski_true() throws ABCException {
		assertTrue(ui.run("verify", "-svcomp16", TestConstants.QUIET,
				filename("szymanski_true-unreach-call.c")));
	}

	@Test
	public void time_var_mutex_true() throws ABCException {
		assertTrue(ui.run("verify", "-svcomp16", TestConstants.QUIET,
				filename("time_var_mutex_true-unreach-call.c")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
