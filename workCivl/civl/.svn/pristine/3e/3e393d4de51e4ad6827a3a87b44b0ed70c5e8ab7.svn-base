package edu.udel.cis.vsl.civl.transform;

import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class CudaTest {

	/* *************************** Static Fields *************************** */

	private static UserInterface ui = new UserInterface();

	private static File rootDir = new File(new File("examples"), "cuda");

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* *************************** Test Methods **************************** */

	@Test
	public void sum() {
		assertTrue(ui.run(
				"verify -enablePrintf=false -inputN=8 -inputNBLOCKS=4",
				filename("sum.cu")));
	}

	@Test
	public void matMult1() {
		assertTrue(ui.run(
				"verify -enablePrintf=false -inputN=2 -inputTILE_WIDTH=1 ",
				filename("matMult1.cu")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
