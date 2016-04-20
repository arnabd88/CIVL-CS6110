package edu.udel.cis.vsl.civl.transform;

import static edu.udel.cis.vsl.civl.TestConstants.NO_PRINTF;
import static edu.udel.cis.vsl.civl.TestConstants.QUIET;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class PthreadTest {
	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"),
			"pthread/esbmc");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods *************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void bigshot_p_false() throws ABCException {
		assertFalse(ui.run("verify", QUIET, "-enablePrintf=false", "-svcomp16",
				filename("bigshot_p_false-unreach-call.c")));
	}

	@Test
	public void bigshot_s_true() throws ABCException {
		assertTrue(ui.run("verify", "-enablePrintf=false", "-svcomp16", QUIET,
				filename("bigshot_s_true-unreach-call.c")));
	}

	@Test
	public void fib_bench_false() throws ABCException {
		assertFalse(ui.run("verify", "-svcomp16", "-inputNUM=5", QUIET,
				NO_PRINTF, filename("fib_bench_false-unreach-call.c")));
	}

	@Test
	public void fib_bench_longer_false() throws ABCException {
		assertFalse(ui.run("verify", "-svcomp16", "-inputNUM=6", QUIET,
				filename("fib_bench_longer_false-unreach-call.c")));
	}

	@Test
	public void fib_bench_true() throws ABCException {
		assertTrue(ui.run("verify", "-svcomp16", "-inputNUM=5", QUIET,
				filename("fib_bench_true-unreach-call.c")));
	}

	@Test
	public void indexer_true() throws ABCException {
		assertTrue(ui.run("verify", "-svcomp16", "-inputSIZE=2", "-inputMAX=4",
				"-inputNUM_THREADS=2", QUIET,
				filename("indexer_true-unreach-call.c")));
	}

	@Test
	public void lazy01_false() throws ABCException {
		assertFalse(ui.run("verify", "-svcomp16", QUIET,
				filename("lazy01_false-unreach-call.c")));
	}

	@Test
	public void queue_false() throws ABCException {
		assertFalse(ui.run("verify", "-svcomp16", "-inputSIZE=5",
				"-inputEMPTY=-1", "-inputFULL=-2", QUIET, NO_PRINTF,
				filename("queue_false-unreach-call.c")));
	}

	@Test
	public void queue_ok_longest_true() throws ABCException {
		assertTrue(ui.run("verify", "-svcomp16", "-inputSIZE=50",
				"-inputEMPTY=-1", "-inputFULL=-2", QUIET, NO_PRINTF,
				filename("queue_ok_longest_true-unreach-call.c")));
	}

	@Test
	public void reorder_2_false() throws ABCException {
		assertFalse(ui.run("verify", "-svcomp16 -debug=false",
				"-input_gen_argc=1", QUIET,
				filename("reorder_2_false-unreach-call.c")));
	}

	@Test
	public void singleton_false() throws ABCException {
		assertFalse(ui.run("verify", "-svcomp16", QUIET,
				filename("singleton_false-unreach-call.c")));
	}

	@Test
	public void singleton_with_uninit_problems_true() throws ABCException {
		assertTrue(ui.run("verify", "-enablePrintf=false", "-svcomp16", QUIET,
				filename("singleton_with-uninit-problems-true.c")));
	}

	@Test
	public void stack_false() throws ABCException {
		assertFalse(ui.run("verify", "-svcomp16", "-inputSIZE=5",
				"-inputOVERFLOW=-1",
				"-inputUNDERFLOW=-2 -input_svcomp_unsigned_bound=8", QUIET,
				NO_PRINTF, filename("stack_false-unreach-call.c")));
	}

	@Test
	public void stack_true() throws ABCException {
		assertTrue(ui.run("verify", "-svcomp16", "-inputSIZE=5",
				"-inputOVERFLOW=-1",
				"-inputUNDERFLOW=-2 -input_svcomp_unsigned_bound=8", QUIET,
				filename("stack_true-unreach-call.c")));
	}

	@Test
	public void stateful01_false() throws ABCException {
		assertFalse(ui.run("verify", "-svcomp16", QUIET,
				filename("stateful01_false-unreach-call.c")));
	}

	@Test
	public void stateful01_true() throws ABCException {
		assertTrue(ui.run("verify", "-svcomp16", QUIET,
				filename("stateful01_true-unreach-call.c")));
	}

	@Test
	public void sync01_true() throws ABCException {
		assertTrue(ui.run("verify", "-svcomp16", QUIET,
				filename("sync01_true-unreach-call.c")));
	}

	@Test
	public void twostage_3_false() throws ABCException {
		assertFalse(ui.run("verify", "-svcomp16", "-input_gen_argc=1", QUIET,
				filename("twostage_3_false-unreach-call.c")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
