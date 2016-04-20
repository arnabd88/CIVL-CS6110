package edu.udel.cis.vsl.civl;

import static edu.udel.cis.vsl.civl.TestConstants.QUIET;
import static edu.udel.cis.vsl.civl.TestConstants.VERIFY;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class VerifyThisTest {
	private static File rootDir = new File(new File("examples"),
			"verifyThisProblems");

	private static UserInterface ui = new UserInterface();

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	@Test
	public void quantifiedComp() {
		assertTrue(ui.run(VERIFY, QUIET, filename("quantifiedComp.cvl")));
	}

	@Test
	public void dancingLinks() {
		assertTrue(ui.run(VERIFY, QUIET, filename("dancingLinks.c")));
	}

	@Test
	public void lcp() {
		assertTrue(ui.run(VERIFY, QUIET, filename("lcp.c")));
	}

	@Test
	public void lrs() {
		assertTrue(ui.run(VERIFY, QUIET, filename("lrs.c")));
	}

	@Test
	public void parallelGCD_2015_2() {
		assertTrue(ui.run(VERIFY, QUIET, filename("parallelGCD.c")));
	}

	@Test
	public void relaxedPrefix_2015_1() {
		assertTrue(ui.run(VERIFY, QUIET, filename("relaxedPrefix.c")));
	}

	@Test
	public void matrixMult() {
		assertTrue(ui.run(VERIFY, QUIET, filename("matrixMult.cvl")));
	}

	@Test
	public void binaryTreeTraversal() {
		assertTrue(ui.run(VERIFY, QUIET, "-inputDB=4",
				filename("binaryTreeTraversal.cvl")));
	}

	@Test
	public void treeBarrier() {
		assertTrue(ui.run(VERIFY, QUIET, filename("treeBarrier.cvl")));
	}

}
