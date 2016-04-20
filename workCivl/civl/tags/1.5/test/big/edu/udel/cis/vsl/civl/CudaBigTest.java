package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class CudaBigTest {

	/* *************************** Static Fields *************************** */

	private static UserInterface ui = new UserInterface();

	private static File rootDir = new File(new File("examples"), "cuda");

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* *************************** Test Methods **************************** */

	@Test
	public void dot() {
		assertTrue(ui
				.run("verify -enablePrintf=false -inputN_B=6 -inputthreadsPerBlock_B=4",
						filename("dot.cu")));
	}

	@Test
	public void cudaOmp() {
		assertTrue(ui.run(
				"verify -enablePrintf=false -inputBLOCK_B=4 -inputTHREADS_B=2",
				filename("cuda-omp.cu")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
