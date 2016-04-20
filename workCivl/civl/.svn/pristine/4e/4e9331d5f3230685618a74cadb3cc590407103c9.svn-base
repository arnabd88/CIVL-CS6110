package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Ignore;
import org.junit.Test;

import edu.udel.cis.vsl.civl.run.UserInterface;

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
		assertFalse(ui.run("verify", filename("hybrid.cvl"), "-inputNPROCS=2"));
	}

	// takes too long: about 90s
	@Ignore
	@Test
	public void hybridMin() {
		assertFalse(ui.run("verify", filename("hybrid.cvl"), "-inputNPROCS=2",
				"-min"));
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
		assertTrue(ui.run("verify", filename("ring.cvl"),
				"-inputNPROCS_BOUND=8", "-inputN_BOUND=4"));
	}

	@Test
	public void ring1() {
		assertTrue(ui.run("verify", filename("ring1.cvl"), "-inputNPROCS=3"));
	}

	@Test
	public void ring2() {
		assertTrue(ui.run("verify", filename("ring2.cvl"), "-inputNPROCS=3"));
	}

	@Test
	public void diffusion1d() {
		assertTrue(ui.run("verify", filename("diffusion1d.cvl"),
				"-inputNPROCSB=3", "-inputNSTEPSB=3", "-inputNXB=6"));
	}
}