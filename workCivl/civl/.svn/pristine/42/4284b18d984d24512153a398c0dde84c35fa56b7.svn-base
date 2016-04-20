package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Ignore;
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
		assertTrue(ui.run("verify", "-svcomp16",
				filename("sync01_true-unreach-call.i")));
	}

	// reorder_2_false-unreach-call.i
	@Test
	public void reorder_2_false() throws ABCException {
		assertFalse(ui.run("verify", "-svcomp16 -showProgram=false",
				filename("reorder_2_false-unreach-call.i")));
	}

	// sigma_false-unreach-call.i
	@Test
	public void sigma_false() throws ABCException {
		assertFalse(ui.run("verify -showProgram=false", "-svcomp16",
				filename("sigma_false-unreach-call.i")));
	}

	// singleton_false-unreach-call.i
	@Test
	public void singleton_false() throws ABCException {
		assertFalse(ui.run("verify", "-svcomp16",
				filename("singleton_false-unreach-call.i")));
	}

	// scull_true-unreach-call.i
	@Ignore
	@Test
	public void scull_true() throws ABCException {
		assertTrue(ui.run("verify", "-svcomp16",
				filename("scull_true-unreach-call.i")));
	}

	// sssc12_variant_true-unreach-call.i
	@Test
	public void sssc12_variant_true() throws ABCException {
		assertTrue(ui.run("verify", "-svcomp16",
				filename("sssc12_variant_true-unreach-call.i")));
	}

	@Test
	public void intPointer() throws ABCException {
		assertTrue(ui.run("verify", "-svcomp16 -pthreadOnly=false",
				filename("intPointer.c")));
	}

	// civl verify -svcomp16 -procBound=10 -checkMemoryLeak=false
	// -input_svcomp_scale=8 pthread/bigshot_p_false-unreach-call.i
	@Ignore
	@Test
	public void mix023_tso() throws ABCException {
		assertFalse(ui.run("verify -showProgram=false", "-svcomp16",
				filename("mix023_tso.opt_false-unreach-call.i")));
	}

	// stack_longest_true-unreach-call.i
	@Test
	public void stack_longest_true() throws ABCException {
		assertTrue(ui.run("verify", "-svcomp16",
				filename("stack_longest_true-unreach-call.i")));
	}

	// mix000_power.oepc_false-unreach-call.i
	@Test
	public void mix000_power() throws ABCException {
		assertFalse(ui.run("verify", "-svcomp16",
				filename("mix000_power.oepc_false-unreach-call.i")));
	}

	// mix000_power.opt_false-unreach-call.i
	@Test
	public void mix000_power_opt() throws ABCException {
		assertFalse(ui.run("verify", "-svcomp16",
				filename("mix000_power.opt_false-unreach-call.i")));
	}

	@Test
	public void gcd_true() throws ABCException {
		assertTrue(ui.run("verify", "-svcomp16",
				filename("gcd_true-unreach-call_true-termination.i")));
		assertTrue(ui.run("verify", "-svcomp16",
				filename("gcd_true-unreach-call_true-termination.i")));
		assertTrue(ui.run("verify", "-svcomp16",
				filename("gcd_true-unreach-call_true-termination.i")));
	}

	// 28_buggy_simple_loop1_vf_false-unreach-call.i
	@Test
	public void buggy_simple_28() throws ABCException {
		assertFalse(ui.run("verify", "-svcomp16",
				filename("28_buggy_simple_loop1_vf_false-unreach-call.i")));
	}

	@Ignore
	@Test
	public void stack_longer_true() {
		assertTrue(ui.run("verify", "-svcomp16",
				filename("25_stack_longer_true-unreach-call.i")));
	}

	@Test
	public void stack_longer_false() {
		assertFalse(ui.run("verify -svcomp16",
				filename("25_stack_longer_false-unreach-call.i")));
	}

	@Test
	public void thread_local() throws ABCException {
		assertTrue(ui.run("verify", "-svcomp16", filename("threadLocal.c")));
	}

	// race-4_2-thread_local_vars_false-unreach-call.i
	@Test
	public void race_4_2() throws ABCException {
		assertFalse(ui.run("verify", "-svcomp16",
				filename("race-4_2-thread_local_vars_false-unreach-call.i")));
	}

	// indexer_true-unreach-call.i
	@Test
	public void indexer_true() {
		assertTrue(ui.run("verify", "-svcomp16",
				filename("indexer_true-unreach-call.i")));
	}

	// 40_barrier_vf_false-unreach-call.i
	@Test
	public void barrier_vf_false() {
		assertFalse(ui.run("verify", "-svcomp16",
				filename("40_barrier_vf_false-unreach-call.i")));
	}

	@Test
	// fk2012_true-unreach-call.i
	public void fk2012_true() {
		assertTrue(ui.run("verify", "-svcomp16",
				filename("fk2012_true-unreach-call.i")));
	}

	// fkp2014_true-unreach-call.i
	@Test
	public void fkp2014_true() {
		assertTrue(ui.run("verify", "-svcomp16",
				filename("fkp2014_true-unreach-call.i")));
	}

	@Test
	// race-2_1-container_of_true-unreach-call.i
	public void race_2_1() {
		assertTrue(ui.run("verify -svcomp16",
				filename("race-2_1-container_of_true-unreach-call.i")));
	}

	// /read_write_lock_true-unreach-call.i
	@Test
	public void read_write_lock() {
		ui.run("verify -svcomp16",
				filename("read_write_lock_true-unreach-call.i"));
		// ui.run("replay -showTransitions -svcomp16",
		// filename("read_write_lock_true-unreach-call.i"));
	}

	@Test
	public void assumefalse() {
		ui.run("verify", filename("atomicAssumeFalse.cvl"));
	}

	// civl show -svcomp16 -pthreadOnly=false -showProgram unsignedInt.c
	@Test
	public void unsignedInt() {
		assertTrue(ui.run("verify", "-svcomp16 -pthreadOnly=false",
				filename("unsignedInt.c")));
	}

	@Test
	public void threadLocal() {
		assertTrue(ui.run("verify", "-svcomp16", filename("threadLocal.c")));
	}

	@Test
	public void fmaxsym_cas_true() {
		ui.run("verify  -svcomp16",
				filename("10_fmaxsym_cas_true-unreach-call.i"));
	}

	@Test
	public void pointerSubtraction() {
		ui.run("verify -svcomp16 -pthreadOnly=false",
				filename("pointerSubtraction.c"));
	}

	@Test
	public void procBound() {
		ui.run("verify -svcomp16 -pthreadOnly=false", filename("procBound.c"));
	}

}
