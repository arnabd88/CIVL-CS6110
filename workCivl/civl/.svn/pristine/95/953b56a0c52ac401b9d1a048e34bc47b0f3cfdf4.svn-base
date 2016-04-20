package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Ignore;
import org.junit.Test;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class PthreadTransformerTest {
	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"),
			"translation/pthread");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods *************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void bigshot_p_false() throws ABCException {
		assertFalse(ui.run("verify", filename("bigshot_s_false.c"), "-enablePrintf=false", "-svcomp"));
	}
	
	@Test
	public void bigshot_s_false() throws ABCException {
		assertFalse(ui.run("verify", filename("bigshot_s_false.c"),	"-enablePrintf=false", "-svcomp"));
	}
	
	@Test
	public void bigshot_s_true() throws ABCException {
		assertTrue(ui.run("verify", filename("bigshot_s_true.c"), "-enablePrintf=false", "-svcomp"));
	}
	
	@Test
	public void fib_bench_false() throws ABCException {
		assertFalse(ui.run("verify", filename("fib_bench_false.c"), "-svcomp", "-inputNUM=5"));
	}
	
	@Test
	public void fib_bench_longer_false() throws ABCException {
		assertFalse(ui.run("verify", filename("fib_bench_longer_false.c"), "-svcomp", "-inputNUM=6"));
	}
	
	@Test
	public void fib_bench_longer_true() throws ABCException {
		assertTrue(ui.run("verify", filename("fib_bench_longer_true.c"), "-svcomp", "-inputNUM=6"));
	}
	
	@Test
	public void fib_bench_longest_false() throws ABCException {
		assertFalse(ui.run("verify", filename("fib_bench_longest_false.c"), "-svcomp", "-inputNUM=11"));
	}
	
	@Test
	public void fib_bench_longest_true() throws ABCException {
		assertTrue(ui.run("verify", filename("fib_bench_longer_true.c"), "-svcomp", "-inputNUM=11"));
	}

	@Test
	public void fib_bench_true() throws ABCException {
		assertTrue(ui.run("verify", filename("fib_bench_true.c"), "-svcomp", "-inputNUM=5"));
	}
	
	@Test
	public void indexer_true() throws ABCException {
		assertTrue(ui.run("verify", filename("indexer_true.c"), "-svcomp", "-inputSIZE=128", "-inputMAX=4", "-inputNUM_THREADS=13"));
	}

	@Test
	public void lazy01_false() throws ABCException {
		assertFalse(ui.run("verify", filename("lazy01_false.c"), "-svcomp"));
	}
	
	@Test
	public void queue_false() throws ABCException {
		assertFalse(ui.run("verify", filename("queue_false.c"), "-svcomp", "inputSIZE=5", "inputEMPTY=-1", "inputFULL=-2"));
	}
	
	@Test
	public void queue_ok_true() throws ABCException {
		assertTrue(ui.run("verify", filename("queue_ok_true.c"), "-svcomp", "inputSIZE=5", "inputEMPTY=-1", "inputFULL=-2"));
	}
	/*
	@Test
	public void reorder_2_false() throws ABCException {
		assertFalse(ui.run("verify", filename("reorder_2_false.c"), "-svcomp"));
	}
	
	@Test
	public void reorder_5_false() throws ABCException {
		assertFalse(ui.run("verify", filename("reorder_5_false.c"), "-svcomp"));
	}
	*/
	@Test
	public void sigma_false() throws ABCException {
		assertFalse(ui.run("verify", filename("sigma_false.c"), "-svcomp"));
	}
	
	@Test
	public void singleton_false() throws ABCException {
		assertFalse(ui.run("verify", filename("singleton_false.c"), "-svcomp"));
	}
	
	@Test
	public void singleton_with_uninit_problems_true() throws ABCException {
		assertTrue(ui.run("verify", filename("singleton_with-uninit-problems-true.c"), "-enablePrintf=false", "-svcomp"));
	}
	
	@Test
	public void stack_false() throws ABCException {
		assertFalse(ui.run("verify", filename("stack_false.c"), "-svcomp", "-inputSIZE=5", "-inputOVERFLOW=-1", "-inputUNDERFLOW=-2"));
	}
	
	@Test
	public void stack_true() throws ABCException {
		assertTrue(ui.run("verify", filename("stack_true.c"), "-svcomp", "-inputSIZE=5", "-inputOVERFLOW=-1", "-inputUNDERFLOW=-2"));
	}

	@Test
	public void stateful01_false() throws ABCException {
		assertFalse(ui.run("verify", filename("stateful01_false.c"), "-svcomp"));
	}
	
	@Test
	public void stateful01_true() throws ABCException {
		assertTrue(ui.run("verify", filename("stateful01_true.c"), "-svcomp"));
	}
	
	@Test
	public void sync01_true() throws ABCException {
		assertTrue(ui.run("verify", filename("sync01_true.c"), "-svcomp"));
	}
	/*
	@Test
	public void twostage_3_false() throws ABCException {
		assertFalse(ui.run("verify", filename("twostage_3_false.c"), "-svcomp"));
	}
	*/
}
