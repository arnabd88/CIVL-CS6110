package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Ignore;
import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class ContractTest {
	/* *************************** Static Fields *************************** */

	private static UserInterface ui = new UserInterface();

	private static File rootDir = new File(new File("examples"), "contracts");

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	@Test
	public void collective_assert() {
		assertFalse(ui.run(
				"verify -enablePrintf=false -input_mpi_nprocs=3 -mpiContract",
				filename("wildcard_coassert_bad.c")));
		assertTrue(ui
				.run("verify -enablePrintf=false -input_mpi_nprocs=4 -deadlock=potential -mpiContract",
						filename("wildcard_coassert_barrier.c")));
		assertTrue(ui
				.run("verify -enablePrintf=false -input_mpi_nprocs=5 -deadlock=potential -mpiContract",
						filename("reduce_coassert.c")));
		assertFalse(ui
				.run("verify -enablePrintf=false -input_mpi_nprocs=4 -deadlock=potential -errorBound=10 -mpiContract",
						filename("wildcard_coassert_bad.c")));
	}

	@Test
	// coverage test: only for covering parts of code, the example may not
	// understandable for human beings.
	public void collective_assert_coverage() {
		assertFalse(ui
				.run("verify -enablePrintf=false -errorBound=10 -input_mpi_nprocs=3 -mpiContract",
						filename("coassert_cover.c")));
	}

	@Test
	public void result() {
		assertTrue(ui
				.run("show -showModel -mpiContract ", filename("result.c")));
	}

	@Ignore
	public void isRecvBufEmpty() {
		assertTrue(ui.run("verify -showModel -mpiContract -input_mpi_nprocs=2",
				filename("isRecvBufEmpty.c")));
	}

	@Test
	public void mergeContracts() {
		assertTrue(ui.run(
				"verify -mpiContract  -deadlock=potential -input_mpi_nprocs=2",
				filename("mergeContracts.c")));
	}

	@Ignore
	public void notEmptyRecvBuf() {
		assertFalse(ui.run("verify -mpiContract -deadlock=potential",
				filename("notEmptyRecvBuf.c")));
	}

	@Test
	public void wildcard_contract_bad() {
		assertFalse(ui
				.run("verify -min -deadlock=potential -mpiContract -input_mpi_nprocs=3",
						filename("wildcard_contract_bad.c")));
		ui.run("replay", filename("wildcard_contract_bad.c"));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
