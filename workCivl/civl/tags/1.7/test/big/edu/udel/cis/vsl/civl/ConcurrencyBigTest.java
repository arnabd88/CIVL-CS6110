package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class ConcurrencyBigTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"),
			"concurrency");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void hybridMin() {
		assertFalse(ui
				.run("verify -inputNPROCS=2 -min", filename("hybrid.cvl")));
	}
	
	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}