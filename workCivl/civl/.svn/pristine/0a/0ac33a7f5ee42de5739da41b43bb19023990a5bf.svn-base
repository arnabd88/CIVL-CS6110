package edu.udel.cis.vsl.civl;

import static edu.udel.cis.vsl.civl.TestConstants.QUIET;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class PthreadBigTest {
	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples", "pthread"),
			"esbmc");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods *************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void fib_bench_longer_true() throws ABCException {
		assertTrue(ui.run("verify", "-svcomp16", "-inputNUM=6",
				filename("fib_bench_longer_true-unreach-call.c")));
	}

	@Test
	public void sigma_false() throws ABCException {
		assertFalse(ui.run("verify", "-svcomp16", QUIET,
				filename("sigma_false-unreach-call.i")));
	}

	@Test
	public void reorder_5_false() throws ABCException {
		assertFalse(ui.run("verify", "-svcomp16", "-input_gen_argc=1", QUIET,
				filename("reorder_5_false-unreach-call.i")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
