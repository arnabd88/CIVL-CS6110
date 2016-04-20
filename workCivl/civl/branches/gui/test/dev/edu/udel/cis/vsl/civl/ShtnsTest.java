package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class ShtnsTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(
			new File(new File("examples"), "omp"), "shtns");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void time_SHT() {
		assertTrue(ui.run("show", "-ompNoSimplify -debug",
				"-input_omp_thread_max=1",
				"-userIncludePath=examples/omp/shtns/SHT:examples/omp/shtns",
				"-sysIncludePath=examples/omp/shtns/SHT:examples/omp/shtns",
				filename("time_SHT.c")));

	}

}
