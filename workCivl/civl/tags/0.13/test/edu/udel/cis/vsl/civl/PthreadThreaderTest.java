package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Ignore;
import org.junit.Test;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class PthreadThreaderTest {
	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"),
			"translation/pthread/threader/");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods *************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */
	
	@Test
	public void dekker_true() throws ABCException {
		assertTrue(ui.run("verify", filename("dekker_true.c"), "-svcomp"));
	}
	
	@Test
	public void lamport_true() throws ABCException {
		assertTrue(ui.run("verify", filename("lamport_true.c"), "-svcomp"));
	}
	
	@Test
	public void peterson_true() throws ABCException {
		assertTrue(ui.run("verify", filename("peterson_true.c"), "-svcomp"));
	}

	@Test
	public void qrcu_false() throws ABCException {
		assertFalse(ui.run("verify", filename("qrcu_false.c"), "-svcomp"));
	}
	
	@Test
	public void qrcu_true() throws ABCException {
		assertTrue(ui.run("verify", filename("qrcu_true.c"), "-svcomp"));
	}
	
	@Test
	public void read_write_lock_false() throws ABCException {
		assertFalse(ui.run("verify", filename("read_write_lock_false.c"), "-svcomp"));
	}
	
	@Test
	public void read_write_lock_true() throws ABCException {
		assertTrue(ui.run("verify", filename("read_write_lock_true.c"), "-svcomp"));
	}
	
	@Ignore
	@Test
	public void scull_true() throws ABCException {
		assertTrue(ui.run("verify", filename("scull_true.c"), "-svcomp"));
	}
	
	@Test
	public void szymanski_true() throws ABCException {
		assertTrue(ui.run("verify", filename("szymanski_true.c"), "-svcomp"));
	}
	
	@Test
	public void time_var_mutex_true() throws ABCException {
		assertTrue(ui.run("verify", filename("time_var_mutex_true.c"), "-svcomp"));
	}
	
}
