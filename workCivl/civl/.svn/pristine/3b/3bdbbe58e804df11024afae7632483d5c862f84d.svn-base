package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.civl.run.UserInterface;

public class CudaTest {

	/***************************** Static Fields *****************************/

	private static UserInterface ui = new UserInterface();

	private static File rootDir = new File(new File("examples"), "cuda");

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/***************************** Test Methods *****************************/

	@Test
	public void exitBarrier() {
		assertTrue(ui.run("verify", filename("exitBarrier.cvl"), "-por=scp"));
	}

	// @Test
	// public void pathfinder() {
	// assertTrue(ui.run("verify", filename("pathfinder.cvl"), "-por=scp"));
	// }
}
