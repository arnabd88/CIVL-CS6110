package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class CgTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "cg");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void cg2Test() {
		assertTrue(ui.run("verify", filename("cg2.cvl")));
	}

	@Test
	public void cg2SylvesterTest() {
		assertTrue(ui.run("verify", filename("cg2_sylvester.cvl")));
	}

	@Test
	public void cg2CholeskyTest() {
		assertTrue(ui.run("verify", filename("cg2_cholesky.cvl")));
	}

	@Test
	public void cg3Test() {
		assertTrue(ui.run("verify", filename("cg3.cvl")));
	}

	@Test
	public void cg3SylvesterTest() {
		assertTrue(ui.run("verify", filename("cg3_sylvester.cvl")));
	}

	@Test
	public void cg3CholeskyTest() {
		assertTrue(ui.run("verify", filename("cg3_cholesky.cvl")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
