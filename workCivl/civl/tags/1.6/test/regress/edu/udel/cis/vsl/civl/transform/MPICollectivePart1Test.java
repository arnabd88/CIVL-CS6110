package edu.udel.cis.vsl.civl.transform;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class MPICollectivePart1Test {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(
			new File(new File("examples"), "mpi"), "collective");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void vectorSum() {
		assertTrue(ui
				.run("verify -input_mpi_nprocs=5", filename("vectorSum.c")));
	}

	@Test
	public void vectorSum_bad() {
		assertFalse(ui.run("verify -input_mpi_nprocs=5",
				filename("vectorSum_bad.c")));
	}

	@Test
	public void bcast_bad() {
		assertFalse(ui.run("verify -input_mpi_nprocs=6 ",
				filename("bcast_bad.c")));
	}

	@Test
	public void bcast_bad_but_ok() {
		assertTrue(ui.run("verify -input_mpi_nprocs=4 ",
				filename("bcast_bad.c")));
	}

	@Test
	public void bcast_good() {
		assertFalse(ui.run("verify -DFASSERT -input_mpi_nprocs=3 ",
				filename("bcast_good.c")));
		assertTrue(ui.run("verify -input_mpi_nprocs=3",
				filename("bcast_good.c")));
	}

	@Test
	public void BcastReduce() {
		assertTrue(ui.run("verify -input_mpi_nprocs=5 ",
				filename("BcastReduce.c")));
	}

	@Test
	public void BcastReduce_bad() {
		assertFalse(ui.run("verify -input_mpi_nprocs=10 ",
				filename("BcastReduce_bad.c")));
	}

	@Test
	public void BcastReduce2() {
		assertTrue(ui.run("verify -input_mpi_nprocs=5 ",
				filename("BcastReduce2.c")));
	}

	@Test
	public void BcastReduce2_bad() {
		assertFalse(ui.run("verify -input_mpi_nprocs=10 ",
				filename("BcastReduce2.c")));
	}

	@Test
	public void gather_order() {
		assertFalse(ui.run("verify -input_mpi_nprocs=6 ", filename("gather.c")));
	}

	@Test
	public void gather_type() {
		assertFalse(ui.run("verify -DTYPE -input_mpi_nprocs=6 ",
				filename("gather.c")));
	}

	@Test
	public void gather_root() {
		assertFalse(ui.run("verify -DROOT -input_mpi_nprocs=6 ",
				filename("gather.c")));
	}

	@Test
	public void gather_good() {
		assertTrue(ui.run("verify -input_mpi_nprocs=2 ", filename("gather.c")));
	}

	@Test
	public void scatter_good() {
		assertTrue(ui.run("verify -input_mpi_nprocs=2 ", filename("scatter.c")));
	}

	@Test
	public void scatter_order() {
		assertFalse(ui
				.run("verify -input_mpi_nprocs=6 ", filename("scatter.c")));
	}

	@Test
	public void scatter_type() {
		assertFalse(ui.run("verify -DTYPE -input_mpi_nprocs=6 ",
				filename("scatter.c")));
	}

	@Test
	public void scatter_root() {
		assertFalse(ui.run("verify -DROOT -input_mpi_nprocs=6 ",
				filename("scatter.c")));
	}

	@Test
	public void scatter2() {
		assertFalse(ui.run("verify -input_mpi_nprocs=6 ",
				filename("scatter2.c")));
	}

	@Test
	public void scatterAllgather_bad() {
		assertFalse(ui.run("verify -input_mpi_nprocs=3 ",
				filename("scatterAllgather_bad.c")));
	}

	@Test
	public void scatterAllgather() {
		assertTrue(ui.run("verify -input_mpi_nprocs=6 ",
				filename("scatterAllgather.c")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
