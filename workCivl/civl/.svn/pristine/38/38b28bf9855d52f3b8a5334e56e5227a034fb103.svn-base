package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class HybridTest {
	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "translation");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods *************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void mpipthreads_both() throws ABCException {
		// assertTrue(ui.run("verify",
		// filename("mpi-pthread/mpithreads_both.c"),
		// "-input__NPROCS=3", "-showInputs", "-enablePrintf=false"));
		ui.run("show", "-showProgram",
				filename("mpi-pthread/mpithreads_both.c"));
		// ui.run("verify", filename("mpi-pthread/mpithreads_both.c"),
		// "-input__NPROCS=3", "-showInputs", "-enablePrintf=false");
		// ui.run("replay", filename("mpi-pthread/mpithreads_both.c"), "-gui");
	}

	@Test
	public void mpi_pthreads_pie_collective() throws ABCException {
		assertTrue(ui.run("verify", "-input__NPROCS=2", "-enablePrintf=false",
				filename("mpi-pthread/mpi-pthreads-pie-collective.c")));
	}
	
	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
