package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class TmpContractTest {
	/* *************************** Static Fields *************************** */

	private static String enableContract = "-mpiContract";

	private static File rootDir = new File(new File("examples"), "experimental");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void seq_sum() {
		assertTrue(ui.run("verify -errorBound=10", enableContract,
				filename("sequential/sum.c")));
	}

	@Test
	public void pointers() {
		assertTrue(ui.run("verify -errorBound=10", enableContract,
				filename("sequential/pointers.c")));
	}

	@Test
	public void pointersBad() {
		assertFalse(ui.run("verify  -errorBound=10", enableContract,
				filename("sequential/pointersBad.c")));
	}

	@Test
	public void pointers2() {
		assertTrue(ui.run("verify  -errorBound=10", enableContract,
				filename("sequential/pointers2.c")));
	}

	@Test
	public void pointers2Bad() {
		assertFalse(ui.run("verify  -errorBound=10", enableContract,
				filename("sequential/pointers2Bad.c")));
	}

	@Test
	public void pointers2Bad2() {
		assertFalse(ui.run("verify  -errorBound=10", enableContract,
				filename("sequential/pointers2Bad2.c")));
	}

	@Test
	public void pointers3() {
		assertTrue(ui.run("verify  -errorBound=10", enableContract,
				filename("sequential/pointers3.c")));
	}

	@Test
	public void pointers3Bad() {
		assertFalse(ui.run("verify  -errorBound=10", enableContract,
				filename("sequential/pointers3Bad.c")));
	}

	@Test
	public void pointers4() {
		assertTrue(ui.run("verify  -showProgram -errorBound=10",
				enableContract, filename("sequential/pointers4.c")));
	}

	@Test
	public void pointers4Bad() {
		assertFalse(ui.run("verify  -errorBound=10", enableContract,
				filename("sequential/pointers4Bad.c")));
	}

	@Test
	public void caseVoidPointers() {
		assertTrue(ui.run("verify  -errorBound=10", enableContract,
				filename("sequential/voidPointers.c")));
	}

	@Test
	public void globalPointers() {
		assertTrue(ui.run("verify  -showProgram -errorBound=10",
				enableContract, filename("sequential/globalPointers.c")));
	}

	@Test
	public void globalPointersBad() {
		assertFalse(ui.run("verify  -errorBound=10", enableContract,
				filename("sequential/globalPointersBad.c")));
	}

	/************************ concurrent section ***********************/
	@Test
	public void dummyMPITest() {
		assertTrue(ui
				.run("verify  -input_mpi_nprocs=2 -showProgram -showAmpleSet -errorBound=10",
						enableContract, filename("sequential/dummyMpiTest.c")));
	}

	@Test
	public void simpleMPITest() {
		assertTrue(ui.run(
				"verify  -showAmpleSet -input_mpi_nprocs=2 -errorBound=10",
				enableContract, filename("sequential/simpleMpiTest.c")));
	}

	@Test
	public void simpleMPITest3() {
		assertTrue(ui.run(
				"verify  -showAmpleSet -input_mpi_nprocs=5 -errorBound=10",
				enableContract, filename("sequential/simpleMpiTest3.c")));
	}

	@Test
	public void broadcast() {
		assertTrue(ui.run("verify  -input_mpi_nprocs=4 -errorBound=1",
				enableContract, filename("sequential/broadcast.c")));
	}

	@Test
	public void broadcastBad() {
		assertFalse(ui.run("verify  -input_mpi_nprocs=4 -errorBound=1",
				enableContract, filename("sequential/broadcast_bad.c")));
	}
}
