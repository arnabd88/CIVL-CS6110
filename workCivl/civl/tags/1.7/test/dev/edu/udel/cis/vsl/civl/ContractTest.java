package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static edu.udel.cis.vsl.civl.TestConstants.VERIFY;
import static edu.udel.cis.vsl.civl.TestConstants.QUIET;
import static edu.udel.cis.vsl.civl.TestConstants.MIN;
import static edu.udel.cis.vsl.civl.TestConstants.NO_PRINTF;
import static edu.udel.cis.vsl.civl.TestConstants.MPI_CONTRACT;
import static edu.udel.cis.vsl.civl.TestConstants.POTENTIAL_DEADLOCK;
import static edu.udel.cis.vsl.civl.TestConstants.SHOW;
import static edu.udel.cis.vsl.civl.TestConstants.REPLAY;
import static edu.udel.cis.vsl.civl.TestConstants.errorBound;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Ignore;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class ContractTest {
	/* *************************** Static Fields *************************** */

	private static UserInterface ui = new UserInterface();

	private static File rootDir = new File(new File("examples"), "contracts");

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	@Ignore
	public void collective_assert() {
		assertFalse(ui.run(
				VERIFY, NO_PRINTF, QUIET,
				"-input_mpi_nprocs=3", MPI_CONTRACT,
				filename("wildcard_coassert_bad.c")));
		
		assertTrue(ui
				.run(VERIFY, NO_PRINTF, "-input_mpi_nprocs=4", POTENTIAL_DEADLOCK,
						MPI_CONTRACT, QUIET,
						filename("wildcard_coassert_barrier.c")));
		
		assertTrue(ui
				.run(VERIFY, NO_PRINTF, "-input_mpi_nprocs=5", POTENTIAL_DEADLOCK,
						MPI_CONTRACT, QUIET,
						filename("reduce_coassert.c")));
		
		assertFalse(ui
				.run(VERIFY, NO_PRINTF, "-input_mpi_nprocs=4", POTENTIAL_DEADLOCK,
						errorBound(10), MPI_CONTRACT,
						QUIET, filename("wildcard_coassert_bad.c")));
	}

	@Ignore
	// coverage test: only for covering parts of code, the example may not
	// understandable for human beings.
	public void collective_assert_coverage() {
		assertFalse(ui
				.run(VERIFY, NO_PRINTF, NO_PRINTF, errorBound(10),
						"-input_mpi_nprocs=3", MPI_CONTRACT,
						QUIET, filename("coassert_cover.c")));
	}

	@Ignore
	public void result() {
		assertTrue(ui
				.run(SHOW, MPI_CONTRACT, filename("result.c")));
	}

	@Ignore
	public void isRecvBufEmptyOK() {
		assertTrue(ui.run(VERIFY, MIN, MPI_CONTRACT, "-input_mpi_nprocs=4",
				QUIET, filename("isRecvBufEmpty_OK.c")));
	}

	@Ignore
	public void isEmptyRecvBufBad() {
		assertFalse(ui.run(VERIFY, MPI_CONTRACT, QUIET, filename("isRecvBufEmpty_BAD.c")));
	}

	@Ignore
	public void wildcard_contract_bad() {
		assertFalse(ui
				.run(VERIFY, MIN, POTENTIAL_DEADLOCK, MPI_CONTRACT,
						"-input_mpi_nprocs=3", QUIET,
						filename("wildcard_contract_bad.c")));
		ui.run(REPLAY, QUIET, filename("wildcard_contract_bad.c"));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
