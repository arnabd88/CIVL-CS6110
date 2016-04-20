package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

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
		assertTrue(ui.run("compare", "-inputN=10", "-spec",
				filename("sumNspec.cvl"), "-impl", filename("sumNimpl.cvl")));
	}

	@Test
	public void adder() {
		assertTrue(ui.run("compare", "-showProgram", "-enablePrintf=false", "-inputNPROCSB=2",
				"-inputNB=4", "-spec", filename("adder", "adder_par.cvl"),
				"-impl", filename("adder", "adder_spec.cvl")));
	}

	@Test
	public void max() {
		assertFalse(ui.run("compare -inputB=4 -min -spec",
				filename("max", "max.cvl"), filename("max", "max_seq.cvl"),
				"-impl -inputNPROCS=2 -inputBLOCK_SIZE=2",
				filename("max", "max.cvl"), filename("max", "max_par.cvl")));
		assertFalse(ui.run("replay -min -spec", filename("max", "max.cvl"),
				filename("max", "max_seq.cvl"), "-impl",
				filename("max", "max.cvl"), filename("max", "max_par.cvl")));
	}

	@Test
	public void dotMpiPthreads() {
		assertTrue(ui
				.run("compare -enablePrintf=false -inputVECLEN=5 -spec -inputMAXTHRDS=2",
						filename("dot", "mpithreads_threads.c"),
						"-impl -input_mpi_nprocs=2",
						filename("dot", "mpithreads_mpi.c")));
	}

	@Test
	public void dotMpiSerial() {
		assertFalse(ui.run("compare -enablePrintf=false -inputVECLEN=5 -spec",
				filename("dot", "mpithreads_serial.c"),
				"-impl -input_mpi_nprocs=2", filename("dot", "mpithreads_mpi.c")));
		assertFalse(ui.run("replay -spec",
				filename("dot", "mpithreads_serial.c"),
				"-impl -input_mpi_nprocs=2", filename("dot", "mpithreads_mpi.c")));
	}

	@Test
	public void dotPthreadsSerial() {
		assertFalse(ui.run("compare -enablePrintf=false -inputVECLEN=5 -spec",
				filename("dot", "mpithreads_serial.c"),
				"-impl -inputMAXTHRDS=2",
				filename("dot", "mpithreads_threads.c")));
	}

	@Test
	public void dotHybridSerial() {
		assertFalse(ui.run("compare -enablePrintf=false -inputVECLEN=5 -spec",
				filename("dot", "mpithreads_serial.c"),
				"-impl -input_mpi_nprocs=2 -inputMAXTHRDS=2",
				filename("dot", "mpithreads_both.c")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
