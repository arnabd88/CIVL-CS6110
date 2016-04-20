package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;

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
		assertTrue(ui.run("verify -showUnreached=true -analyze_abs=false",
				filename("unreached.c")));
	}

	@Test
	public void abs() {
		assertTrue(ui.run("verify -analyze_abs=true -showUnreached=false",
				filename("abs.c")));
	}

	@Test
	public void abs2() {
		assertTrue(ui.run("verify -analyze_abs=true -showUnreached=false",
				filename("abs2.c")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
