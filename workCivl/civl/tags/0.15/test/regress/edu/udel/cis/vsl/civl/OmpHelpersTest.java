package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class OmpHelpersTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "library/omp");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void teams() {
		assertTrue(ui.run("run", filename("teams.cvl")));
	}

	@Test
	public void shared() {
		assertTrue(ui.run("run", filename("shared.cvl")));
	}

	// TODO: move this to another test. it has nothing to do with omp.
	@Test
	public void read() {
		assertTrue(ui.run("run", filename("read.cvl")));
	}

	@Test
	public void write() {
		assertTrue(ui.run("run", filename("write.cvl")));
	}

	@Test
	public void barrierFlush() {
		// assertTrue(ui.run("run", filename("barrierFlush.cvl"),
		// "-showSavedStates"));
		assertTrue(ui.run("run", filename("barrierFlush.cvl")));
		// ui.run("run", filename("barrierFlush.cvl"));
		// ui.run("replay", "-gui", filename("barrierFlush.cvl"));
	}

	@Test
	public void reduction() {
		assertTrue(ui.run("run", filename("reduction.cvl")));
	}

	@Test
	public void sections() {
		assertTrue(ui.run("run", filename("sections.cvl")));
	}

	@Test
	public void single() {
		assertTrue(ui.run("run", filename("single.cvl")));
	}

	@Test
	public void ompfor() {
		assertTrue(ui.run("run", filename("for.cvl")));
	}
}
