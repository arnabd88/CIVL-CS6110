package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class GenTransformerTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "gen");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void gen() {
		assertTrue(ui.run("verify -showProgram -enablePrintf=false",
				filename("gen.c")));
	}

	@Test
	public void gen_argc() {
		assertTrue(ui.run("verify -showProgram -input_gen_argc=5",
				filename("gen.c")));
	}

	@Test
	public void simpleMPI() {
		assertTrue(ui.run(
				"verify -input_mpi_nprocs=2 -showProgram -enablePrintf=false",
				filename("simpleMPI.c")));
	}

	@Test
	public void simpleMPI2() {
		assertTrue(ui.run(
				"verify -showProgram -input_mpi_nprocs=2 -enablePrintf=false",
				filename("simpleMPI2.c")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
