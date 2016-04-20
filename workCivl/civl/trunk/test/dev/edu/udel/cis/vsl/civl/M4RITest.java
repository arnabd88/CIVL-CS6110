package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class M4RITest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(
			new File(new File("examples"), "omp"), "m4ri");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void m4riShow() {
		assertTrue(ui.run("show", "-showProgram", "-ompNoSimplify",
				"-sysIncludePath=examples/omp/m4ri/m4ri:examples/omp/m4ri",
				filename("tests/test_colswap.c"),
				/*filename("m4ri/brilliantrussian.c"),
				filename("m4ri/debug_dump.c"), filename("m4ri/djb.c"),
				filename("m4ri/echelonform.c"), filename("m4ri/graycode.c"),
				filename("m4ri/io.c"), filename("m4ri/misc.c"),
				filename("m4ri/mmc.c"), filename("m4ri/mp.c"),
				filename("m4ri/mzd.c"), filename("m4ri/mzp.c"),
				filename("m4ri/ple_russian.c"), filename("m4ri/ple.c"),
				filename("m4ri/solve.c"), filename("m4ri/strassen.c"),
				filename("m4ri/triangular_russian.c"),*/
				filename("m4ri/triangular.c")));

	}

	@Test
	public void m4riVerify() {
		assertTrue(ui.run("verify", "-ompNoSimplify",
				"-userIncludePath=examples/omp/m4ri/m4ri:examples/omp/m4ri",
				"-sysIncludePath=examples/omp/m4ri/m4ri:examples/omp/m4ri",
				filename("tests/test_colswap.c"),
				filename("m4ri/brilliantrussian.c"),
				filename("m4ri/debug_dump.c"), filename("m4ri/djb.c"),
				filename("m4ri/echelonform.c"), filename("m4ri/graycode.c"),
				filename("m4ri/io.c"), filename("m4ri/misc.c"),
				filename("m4ri/mmc.c"), filename("m4ri/mp.c"),
				filename("m4ri/mzd.c"), filename("m4ri/mzp.c"),
				filename("m4ri/ple_russian.c"), filename("m4ri/ple.c"),
				filename("m4ri/solve.c"), filename("m4ri/strassen.c"),
				filename("m4ri/triangular_russian.c"),
				filename("m4ri/triangular.c")));

	}

}
