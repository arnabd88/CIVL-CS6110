package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class ExperimentalTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "experimental");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void arrayWrite() {
		assertTrue(ui.run("run", filename("arrayWrite.cvl")));
	}

	@Test
	public void ring3ModelBug() {
		assertTrue(ui.run("verify", filename("ring3ModelBug.cvl")));
	}

	@Test
	public void diff1dCompare() {
		assertTrue(ui.run("compare", "-spec", filename("diff1d_spec.c"),
				"-impl", filename("diff1d_par.c")));
	}

	@Test
	public void treeFalse() {
		assertTrue(ui.run("verify", filename("tree_false-unreach-call.c")));
	}

	@Test
	public void mergeSort() {
		assertTrue(ui.run("verify -showProgram",
				filename("merge_sort_false-unreach-call.c")));
	}

	@Test
	public void moPie() {
		assertTrue(ui
				.run("show -showProgram -input_NPROCS=2 -ompNoSimplify -inputTHREAD_MAX=2 ",
						filename("mpi-omp-pie-calculation.c")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
