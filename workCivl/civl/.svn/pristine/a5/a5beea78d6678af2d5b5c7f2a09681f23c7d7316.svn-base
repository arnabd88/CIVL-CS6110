package edu.udel.cis.vsl.civl.transform;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static edu.udel.cis.vsl.civl.TestConstants.NO_PRINTF;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.civl.TestConstants;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class MPICollectivePart2Test {

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
	public void scatterGather_bad() {
		assertFalse(ui.run("verify -DORDER -input_mpi_nprocs=6 ",
				TestConstants.QUIET, filename("scatterGather.c")));
	}

	@Test
	public void scatterGather() {
		assertTrue(ui.run("verify -input_mpi_nprocs=6 ",
				TestConstants.QUIET, NO_PRINTF, filename("scatterGather.c")));
	}

	@Test
	public void bcast_ex04() {
		assertTrue(ui.run("verify -input_mpi_nprocs=6 ", TestConstants.QUIET, 
				NO_PRINTF, filename("c_ex04.c")));
	}

	@Test
	public void scatterGather_ex05() {
		assertTrue(ui.run("verify -input_mpi_nprocs=6 -inputcount=5",
				TestConstants.QUIET, NO_PRINTF, filename("c_ex05.c")));
	}

	@Test
	public void scatterReduce_ex06() {
		assertTrue(ui.run("verify -input_mpi_nprocs=6 -inputcount=5",
				TestConstants.QUIET, NO_PRINTF, filename("c_ex06.c")));
	}

	@Test
	public void alltoall_ex07() {
		assertTrue(ui.run("verify -enablePrintf=false -input_mpi_nprocs=6 ",
				TestConstants.QUIET, NO_PRINTF, filename("c_ex07.c")));
	}

	@Test
	public void gatherv_ex08() {
		assertTrue(ui.run("verify -input_mpi_nprocs=6 ", TestConstants.QUIET, 
				NO_PRINTF, filename("c_ex08.c")));
	}

	@Test
	public void gatherv_ex13() {
		assertTrue(ui.run("verify -input_mpi_nprocs=6 ", TestConstants.QUIET, 
				NO_PRINTF, filename("c_ex13.c")));
	}

	@Test
	public void alltoallv() {
		assertTrue(ui.run("verify -input_mpi_nprocs=6 ",
				TestConstants.QUIET, NO_PRINTF, filename("alltoallv.c")));
	}

	@Test
	public void reduce() {
		assertTrue(ui.run("verify -input_mpi_nprocs=6", TestConstants.QUIET, 
				NO_PRINTF, filename("reduce.c")));
	}

	@Test
	public void reduce_operator() {
		assertFalse(ui.run("verify -input_mpi_nprocs=6 -DOPERATOR",
				TestConstants.QUIET, filename("reduce.c")));
	}

	@Test
	public void reduce_root() {
		assertFalse(ui.run("verify -input_mpi_nprocs=6 -DROOT",
				TestConstants.QUIET, filename("reduce.c")));
	}

	@Test
	public void reduce_type() {
		assertFalse(ui.run("verify -input_mpi_nprocs=6 -DTYPE",
				TestConstants.QUIET, filename("reduce.c")));
	}

	@Test
	public void allreduce() {
		assertTrue(ui
				.run("verify -input_mpi_nprocs=6", TestConstants.QUIET, 
						NO_PRINTF, filename("allreduce.c")));
	}

	@Test
	public void allreduce_operator() {
		assertFalse(ui.run("verify -input_mpi_nprocs=6 -DOPERATOR",
				TestConstants.QUIET, filename("allreduce.c")));
	}

	@Test
	public void allreduce_type() {
		assertFalse(ui.run("verify -input_mpi_nprocs=6 -DTYPE",
				TestConstants.QUIET, filename("allreduce.c")));
	}

	@Test
	public void barrierReduce() {
		assertTrue(ui.run("verify -input_mpi_nprocs=5",
				TestConstants.QUIET, NO_PRINTF, filename("barrierReduce.c")));
	}

	@Test
	public void barrierReduce_order() {
		assertFalse(ui.run("verify -input_mpi_nprocs=5 -DORDER",
				TestConstants.QUIET, NO_PRINTF, filename("barrierReduce.c")));
	}

	@Test
	public void barrierScatter() {
		assertFalse(ui.run("verify -input_mpi_nprocs=5",
				TestConstants.QUIET, filename("barrierScatter.c")));
	}

	@Test
	public void reduceScatter() {
		assertTrue(ui.run("verify -input_mpi_nprocs=4",
				TestConstants.QUIET, NO_PRINTF, filename("reduceScatter.c")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
