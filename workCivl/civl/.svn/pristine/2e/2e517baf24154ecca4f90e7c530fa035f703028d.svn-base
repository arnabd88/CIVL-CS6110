package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Ignore;
import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class MessagePassingTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"),
			"messagePassing");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void hybrid() {
		assertFalse(ui.run("verify", "-inputNPROCS=2", filename("hybrid.cvl")));
	}

	@Test
	public void mpiPthreads() {
		assertFalse(ui.run("verify", filename("mpi-pthreads.cvl")));
	}

	@Test
	public void mpiPthreadsMin() {
		assertFalse(ui.run("verify", "-min", filename("mpi-pthreads.cvl")));
	}

	@Test
	public void ring() {
		assertTrue(ui.run("verify", "-inputNPROCS_BOUND=8", "-inputN_BOUND=4",
				filename("ring.cvl")));
	}

	@Test
	public void ring1() {
		assertTrue(ui.run("verify", "-inputNPROCS=3", filename("ring1.cvl")));
	}

	@Ignore
	@Test
	public void ring2() {
		assertTrue(ui.run("verify", "-inputNPROCS=3", filename("ring2.cvl")));
	}

	@Test
	public void wildcard() {
		assertTrue(ui.run("verify", "-inputNPROCS=5", "-enablePrintf=false",
				filename("wildcard.cvl")));
	}

	@Test
	public void wildcardBad() {
		assertFalse(ui.run("verify", "-enablePrintf=false",
				filename("wildcardBad.cvl")));
		ui.run("replay", filename("wildcardBad.cvl"));
	}
}