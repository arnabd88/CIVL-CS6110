package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;
import static edu.udel.cis.vsl.civl.TestConstants.ANALYZE_ABS;
import static edu.udel.cis.vsl.civl.TestConstants.VERIFY;
import static edu.udel.cis.vsl.civl.TestConstants.QUIET;
import static edu.udel.cis.vsl.civl.TestConstants.NO_PRINTF;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class AnalysisTest {
	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "analysis");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void unreached() {
		assertTrue(ui.run(VERIFY, QUIET, NO_PRINTF, filename("unreached.c")));
	}

	@Test
	public void abs() {
		assertTrue(ui.run(VERIFY, ANALYZE_ABS, QUIET, filename("abs.c")));
	}

	@Test
	public void abs2() {
		assertTrue(ui.run(VERIFY, ANALYZE_ABS, QUIET, filename("abs2.c")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
