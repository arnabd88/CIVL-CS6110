package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class SvcompTest {
	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples", "pthread"),
			"svcomp");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods *************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	// Yes
	// None
	@Test
	public void sync01_true() throws ABCException {
		assertTrue(ui.run("verify", "-svcomp16", TestConstants.QUIET,
				filename("sync01_true-unreach-call.i")));
	}

	// reorder_2_false-unreach-call.i
	@Test
	public void reorder_2_false() throws ABCException {
		assertFalse(ui
				.run("verify", "-svcomp16 -showProgram=false",
						TestConstants.QUIET,
						filename("reorder_2_false-unreach-call.i")));
	}

	// sigma_false-unreach-call.i
	@Test
	public void sigma_false() throws ABCException {
		assertFalse(ui.run("verify -showProgram=false", "-svcomp16",
				TestConstants.QUIET, filename("sigma_false-unreach-call.i")));
	}

	// singleton_false-unreach-call.i
	@Test
	public void singleton_false() throws ABCException {
		assertFalse(ui.run("verify", "-svcomp16", TestConstants.QUIET,
				filename("singleton_false-unreach-call.i")));
	}

	@Test
	public void intPointer() throws ABCException {
		assertTrue(ui.run("verify", "-svcomp16", TestConstants.QUIET,
				filename("intPointer.c")));
	}

	@Test
	public void mix023_tso() throws ABCException {
		assertFalse(ui.run("verify -showProgram=false", "-svcomp16",
				TestConstants.QUIET,
				filename("mix023_tso.opt_false-unreach-call.i")));
	}

	// stack_longest_true-unreach-call.i
	@Test
	public void stack_longest_true() throws ABCException {
		assertTrue(ui.run("verify", "-svcomp16", TestConstants.QUIET,
				filename("stack_longest_true-unreach-call.i")));
	}

	// mix000_power.oepc_false-unreach-call.i
	@Test
	public void mix000_power() throws ABCException {
		assertFalse(ui.run("verify", "-svcomp16", TestConstants.QUIET,
				filename("mix000_power.oepc_false-unreach-call.i")));
	}

	// mix000_power.opt_false-unreach-call.i
	@Test
	public void mix000_power_opt() throws ABCException {
		assertFalse(ui.run("verify", "-svcomp16", TestConstants.QUIET,
				filename("mix000_power.opt_false-unreach-call.i")));
	}

	@Test
	public void gcd_true() throws ABCException {
		assertTrue(ui.run("verify", "-svcomp16", TestConstants.QUIET,
				filename("gcd_true-unreach-call_true-termination.i")));
	}

	// 28_buggy_simple_loop1_vf_false-unreach-call.i
	@Test
	public void buggy_simple_28() throws ABCException {
		assertFalse(ui.run("verify", "-svcomp16", TestConstants.QUIET,
				filename("28_buggy_simple_loop1_vf_false-unreach-call.i")));
	}

	@Test
	public void thread_local() throws ABCException {
		assertTrue(ui.run("verify", "-svcomp16", TestConstants.QUIET,
				filename("threadLocal.c")));
	}

	@Test
	public void threadLocal() {
		assertTrue(ui.run("verify", "-svcomp16", TestConstants.QUIET,
				filename("threadLocal.c")));
	}

	@Test
	public void fmaxsym_cas_true() {
		assertTrue(ui.run("verify  -svcomp16", TestConstants.QUIET,
				filename("10_fmaxsym_cas_true-unreach-call.i")));
	}
}
