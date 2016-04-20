package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Ignore;
import org.junit.Test;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class PthreadCProverTest {
	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"),
			"translation/pthread/cprover/");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods *************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Ignore
	@Test
	public void inc_true() throws ABCException {
		assertTrue(ui.run("verify", filename("01_inc_true.c"), "-svcomp"));
	}

	@Ignore
	@Test
	public void inc_cas_true() throws ABCException {
		assertTrue(ui.run("verify", filename("02_inc_cas_true.c"), "-svcomp"));
	}

	@Ignore
	@Test
	public void incdec_true() throws ABCException {
		assertTrue(ui.run("verify", filename("03_incdec_true.c"), "-svcomp"));
	}

	@Ignore
	@Test
	public void incdec_cas_true() throws ABCException {
		assertTrue(ui
				.run("verify", filename("04_incdec_cas_true.c"), "-svcomp"));
	}

	@Ignore
	@Test
	public void tas_true() throws ABCException {
		assertTrue(ui.run("verify", filename("05_tas_true.c"), "-svcomp"));
	}

	@Ignore
	@Test
	public void ticket_true() throws ABCException {
		assertTrue(ui.run("verify", filename("06_ticket_true.c"), "-svcomp"));
	}

	@Ignore
	@Test
	public void rand_true() throws ABCException {
		assertTrue(ui.run("verify", filename("07_rand_true.c"), "-svcomp"));
	}

	@Ignore
	@Test
	public void rand_cas_true() throws ABCException {
		assertTrue(ui.run("verify", filename("08_rand_cas_true.c"), "-svcomp"));
	}

	@Ignore
	@Test
	public void fmaxsym_true() throws ABCException {
		assertTrue(ui.run("verify", filename("09_fmaxsym_true.c"), "-svcomp"));
	}

	@Ignore
	@Test
	public void fmaxsym_cas_true() throws ABCException {
		assertTrue(ui.run("verify", filename("10_fmaxsym_cas_true.c"),
				"-svcomp"));
	}

	@Ignore
	@Test
	public void fmaxsymopt_true() throws ABCException {
		assertTrue(ui
				.run("verify", filename("11_fmaxsymopt_true.c"), "-svcomp"));
	}

	@Ignore
	@Test
	public void fmaxsymopt_cas_true() throws ABCException {
		assertTrue(ui.run("verify", filename("12_fmaxsymopt_cas_true.c"),
				"-svcomp"));
	}

	@Ignore
	@Test
	public void unverif_true() throws ABCException {
		assertTrue(ui.run("verify", filename("13_unverif_true.c"), "-svcomp"));
	}

	@Ignore
	@Test
	public void spin2003_true() throws ABCException {
		assertTrue(ui.run("verify", filename("14_spin2003_true.c"), "-svcomp"));
	}

	@Ignore
	@Test
	public void dekker_true() throws ABCException {
		assertTrue(ui.run("verify", filename("15_dekker_true.c"), "-svcomp"));
	}

	@Ignore
	@Test
	public void peterson_true() throws ABCException {
		assertTrue(ui.run("verify", filename("16_peterson_true.c"), "-svcomp"));
	}

	@Ignore
	@Test
	public void szymanski_true() throws ABCException {
		assertTrue(ui.run("verify", filename("17_szymanski_true.c"), "-svcomp"));
	}

	@Ignore
	@Test
	public void read_write_lock_true() throws ABCException {
		assertTrue(ui.run("verify", filename("18_read_write_lock_true.c"),
				"-svcomp"));
	}

	@Ignore
	@Test
	public void time_var_mutex_true() throws ABCException {
		assertTrue(ui.run("verify", filename("19_time_var_mutex_true.c"),
				"-svcomp"));
	}

	@Ignore
	@Test
	public void lamport_true() throws ABCException {
		assertTrue(ui.run("verify", filename("20_lamport_true.c"), "-svcomp"));
	}

	@Ignore
	@Test
	public void lu_fig2_fixed_true() throws ABCException {
		assertTrue(ui.run("verify", filename("23_lu-fig2.fixed_true.c"),
				"-svcomp"));
	}

	@Ignore
	@Test
	public void stack_true() throws ABCException {
		assertTrue(ui.run("verify", filename("25_stack_true.c"), "-svcomp"));
	}

	@Ignore
	@Test
	public void stack_cas_true() throws ABCException {
		assertTrue(ui.run("verify", filename("26_stack_cas_true.c"), "-svcomp"));
	}

	@Ignore
	@Test
	public void Boop_simple_vf_false() throws ABCException {
		assertFalse(ui.run("verify", filename("27_Boop_simple_vf_false.c"),
				"-svcomp"));
	}

	@Ignore
	@Test
	public void buggy_simple_loop1_vf_false() throws ABCException {
		assertFalse(ui.run("verify",
				filename("28_buggy_simple_loop1_vf_false.c"), "-svcomp"));
	}

	@Ignore
	@Test
	public void conditionals_vs_true() throws ABCException {
		assertTrue(ui.run("verify", filename("29_conditionals_vs_true.c"),
				"-svcomp"));
	}

	@Ignore
	@Test
	public void Function_Pointer3_vs_true() throws ABCException {
		assertTrue(ui.run("verify", filename("30_Function_Pointer3_vs_true.c"),
				"-svcomp"));
	}

	@Ignore
	@Test
	public void simple_loop5_vs_true() throws ABCException {
		assertTrue(ui.run("verify", filename("31_simple_loop5_vs_true.c"),
				"-svcomp"));
	}

	@Ignore
	@Test
	public void pthread5_vs_false() throws ABCException {
		assertTrue(ui.run("verify", filename("32_pthread5_vs_false.c"),
				"-svcomp"));
	}

	@Ignore
	@Test
	public void double_lock_p1_vs_true() throws ABCException {
		assertTrue(ui.run("verify", filename("33_double_lock_p1_vs_true.c"),
				"-svcomp"));
	}

	@Ignore
	@Test
	public void double_lock_p2_vs_true() throws ABCException {
		assertTrue(ui.run("verify", filename("34_double_lock_p2_vs_true.c"),
				"-svcomp"));
	}

	@Ignore
	@Test
	public void double_lock_p3_vs_true() throws ABCException {
		assertTrue(ui.run("verify", filename("35_double_lock_p3_vs_true.c"),
				"-svcomp"));
	}

	@Ignore
	@Test
	public void stack_cas_p0_vs_true() throws ABCException {
		assertTrue(ui.run("verify",
				filename("36_stack_cas_p0_vs_concur_true.c"), "-svcomp"));
	}

	@Ignore
	@Test
	public void stack_lock_p0_vs_true() throws ABCException {
		assertTrue(ui.run("verify",
				filename("37_stack_lock_p0_vs_concur_true.c"), "-svcomp"));
	}

	@Ignore
	@Test
	public void rand_cas_vs_concur_true() throws ABCException {
		assertTrue(ui.run("verify", filename("38_rand_cas_vs_concur_true.c"),
				"-svcomp"));
	}

	@Ignore
	@Test
	public void rand_lock_p0_vs_true() throws ABCException {
		assertTrue(ui.run("verify", filename("39_rand_lock_p0_vs_true.c"),
				"-svcomp"));
	}

	@Ignore
	@Test
	public void barrier_vf_false() throws ABCException {
		assertFalse(ui.run("verify", filename("40_barrier_vf_false.c"),
				"-svcomp"));
	}

	@Ignore
	@Test
	public void FreeBSD__abd_kbd__sliced_true() throws ABCException {
		assertFalse(ui.run("verify",
				filename("41_FreeBSD__abd_kbd__sliced_true.c"), "-svcomp"));
	}

	@Ignore
	@Test
	public void FreeBSD__rdma_addr__sliced_true() throws ABCException {
		assertTrue(ui.run("verify",
				filename("42_FreeBSD__rdma_addr__sliced_true.c"), "-svcomp"));
	}

	@Ignore
	@Test
	public void NetBSD__sysmon_power__sliced_true() throws ABCException {
		assertTrue(ui.run("verify",
				filename("43_NetBSD__sysmon_power__sliced_true.c"), "-svcomp"));
	}

	@Ignore
	@Test
	public void Solaris__space_map__sliced_true() throws ABCException {
		assertTrue(ui.run("verify",
				filename("44_Solaris__space_map__sliced_true.c"), "-svcomp"));
	}

	@Ignore
	@Test
	public void monabsex1_vs_true() throws ABCException {
		assertTrue(ui.run("verify", filename("45_monabsex1_vs_true.c"),
				"-svcomp"));
	}

	@Ignore
	@Test
	public void monabsex2_vs_true() throws ABCException {
		assertTrue(ui.run("verify", filename("46_monabsex2_vs_true.c"),
				"-svcomp"));
	}

	@Ignore
	@Test
	public void ticket_lock_hc_backoff_vs_true() throws ABCException {
		assertTrue(ui.run("verify",
				filename("47_ticket_lock_hc_backoff_vs_true.c"), "-svcomp"));
	}

	@Ignore
	@Test
	public void ticket_lock_low_contention_vs_true() throws ABCException {
		assertTrue(ui.run("verify",
				filename("48_ticket_lock_low_contention_vs_true.c"), "-svcomp"));
	}

	@Ignore
	@Test
	public void fib_bench_longest_false() throws ABCException {
		assertFalse(ui.run("verify", "-svcomp", "-inputNUM=11",
				filename("fib_bench_longest_false.c")));
	}

	@Ignore
	@Test
	public void scull_true() throws ABCException {
		assertTrue(ui.run("verify", "-svcomp", filename("scull_true.c")));
	}

	@Ignore
	@Test
	public void fib_bench_longest_true() throws ABCException {
		assertTrue(ui.run("verify", "-svcomp", "-inputNUM=11",
				filename("fib_bench_longest_true.c")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
