package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static edu.udel.cis.vsl.civl.TestConstants.QUIET;
import static edu.udel.cis.vsl.civl.TestConstants.COMPARE;
import static edu.udel.cis.vsl.civl.TestConstants.SPEC;
import static edu.udel.cis.vsl.civl.TestConstants.IMPL;
import static edu.udel.cis.vsl.civl.TestConstants.NO_PRINTF;
import static edu.udel.cis.vsl.civl.TestConstants.SHOW;
import static edu.udel.cis.vsl.civl.TestConstants.REPLAY;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class CompareTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "compare");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String subfolder, String name) {
		return new File(new File(rootDir, subfolder), name).getPath();
	}

	private static String filename(String name) {
		return filename(".", name);
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void sumN() {
		assertTrue(ui.run(COMPARE, "-inputN=10", QUIET, SPEC, filename("sumNspec.cvl"), 
				IMPL, filename("sumNimpl.cvl")));
	}

	@Test
	public void adder() {
		assertTrue(ui.run(COMPARE, QUIET, NO_PRINTF, "-inputNPROCSB=2", "-inputNB=4", 
				SPEC, filename("adder", "adder_par.cvl"), 
				IMPL, filename("adder", "adder_spec.cvl")));
	}

	@Test
	public void max() {
		ui.run(SHOW, QUIET, filename("max", "max.cvl"), 
				filename("max", "max_seq.cvl"));
		// assertFalse(ui.run("compare -inputB=4 -min -spec",
		// filename("max", "max.cvl"), filename("max", "max_seq.cvl"),
		// "-impl -inputNPROCS=2 -inputBLOCK_SIZE=2",
		// filename("max", "max.cvl"), filename("max", "max_par.cvl")));
		// assertFalse(ui.run("replay -min -spec", filename("max", "max.cvl"),
		// filename("max", "max_seq.cvl"), "-impl",
		// filename("max", "max.cvl"), filename("max", "max_par.cvl")));
	}

	@Test
	public void dotMpiPthreads() {
		assertTrue(ui
				.run(COMPARE, NO_PRINTF, QUIET,
						"-inputVECLEN=5", SPEC,
						"-inputMAXTHRDS=2", filename("dot", "mpithreads_threads.c"),
						IMPL, "-input_mpi_nprocs=2",
						filename("dot", "mpithreads_mpi.c")));
	}

	@Test
	public void dotMpiSerial() {
		assertFalse(ui.run(COMPARE, NO_PRINTF, QUIET,
				"-inputVECLEN=5", SPEC,
				filename("dot", "mpithreads_serial.c"),
				IMPL, "-input_mpi_nprocs=2",
				filename("dot", "mpithreads_mpi.c")));
		
		assertFalse(ui.run(REPLAY, QUIET, NO_PRINTF, SPEC,
				filename("dot", "mpithreads_serial.c"),
				IMPL, "-input_mpi_nprocs=2",
				filename("dot", "mpithreads_mpi.c")));
	}

	@Test
	public void dotPthreadsSerial() {
		assertFalse(ui.run(COMPARE, NO_PRINTF, QUIET,
				"-inputVECLEN=5", SPEC, 
				filename("dot", "mpithreads_serial.c"),
				IMPL, "-inputMAXTHRDS=2",
				filename("dot", "mpithreads_threads.c")));
	}

	@Test
	public void dotHybridSerial() {
		assertFalse(ui.run(COMPARE, NO_PRINTF, QUIET,
				"-inputVECLEN=5", SPEC,
				filename("dot", "mpithreads_serial.c"),
				IMPL, "-input_mpi_nprocs=2 -inputMAXTHRDS=2",
				filename("dot", "mpithreads_both.c")));
	}

	@Test
	public void outputfiles() {
		assertTrue(ui.run(COMPARE, QUIET,
				SPEC, filename("outputTest", "out1.c"),
				IMPL, filename("outputTest", "out2.c")));
	}

	@Test
	public void outputfile() {
		assertTrue(ui.run(COMPARE, QUIET,
				SPEC, filename("outputfile", "spec.c"),
				IMPL, filename("outputfile", "impl.c")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
