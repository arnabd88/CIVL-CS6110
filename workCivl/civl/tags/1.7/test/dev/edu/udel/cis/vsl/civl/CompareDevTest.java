package edu.udel.cis.vsl.civl;

import java.io.File;
import static edu.udel.cis.vsl.civl.TestConstants.COMPARE;
import static edu.udel.cis.vsl.civl.TestConstants.IMPL;
import static edu.udel.cis.vsl.civl.TestConstants.QUIET;
import static edu.udel.cis.vsl.civl.TestConstants.SPEC;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class CompareDevTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "compare");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String subfolder, String name) {
		return new File(new File(rootDir, subfolder), name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void vector() {
		ui.run("verify", filename("sliced_vector", "sliced_vector_addin.c"));
	}

	@Test
	public void queue() {
		ui.run(COMPARE, QUIET, SPEC, filename("queue", "driver.cvl"), filename("queue", "queue_two_lock.c"), IMPL,
				filename("queue", "driver.cvl"), filename("queue", "queue_non_blocking.c"));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
