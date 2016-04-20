package edu.udel.cis.vsl.civl;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class ReductionContractTest {
	/* *************************** Static Fields *************************** */

	private static File rootDir = new File("examples", "contracts");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods *************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void cqueue() {
		ui.run("show -showModel", filename("cqueue.c"));
	}
}
