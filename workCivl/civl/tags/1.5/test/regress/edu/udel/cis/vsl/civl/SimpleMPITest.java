package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Ignore;
import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class SimpleMPITest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(
			new File(new File("examples"), "mpi"), "simple");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void simpleMPI() {
		assertTrue(ui.run("verify -input_mpi_nprocs=2",
				filename("simpleMPI.c")));
	}

	@Test
	public void commDup() {
		assertTrue(ui.run("verify -showAmpleSet -input_mpi_nprocs=6",
				filename("commDup.c")));
	}

	@Test
	public void commDupBad() {
		assertFalse(ui.run("verify -showAmpleSet -input_mpi_nprocs=6",
				filename("commDupBad.c")));
	}

	@Test
	public void anysource() {
		assertTrue(ui.run("verify -input_mpi_nprocs=2", filename("anysource.c")));
	}

	@Test
	public void noInit() {
		assertFalse(ui.run("verify -input_mpi_nprocs=5", filename("noInit.c")));
	}

	@Test
	public void noFinalize() {
		assertFalse(ui.run("verify -input_mpi_nprocs=5", filename("noFinalize.c")));
	}

	@Ignore
	@Test
	public void goodInitFinalize() {
		assertTrue(ui.run("verify -input_mpi_nprocs=5",
				filename("goodInitFinalize.c")));
	}

	@Test
	public void count() {
		assertTrue(ui.run("verify -input_mpi_nprocs=2", filename("count.c")));
	}

	@Test
	public void unreceived() {
		assertFalse(ui.run("verify -input_mpi_nprocs=2", filename("unreceived.c")));
	}

	@Test
	public void bcast() {
		assertTrue(ui.run("verify -input_mpi_nprocs=5", filename("bcast.c")));
	}

	@Test
	public void bcast_int() {
		assertTrue(ui.run("verify -input_mpi_nprocs=5", filename("bcast_int.c")));
	}

	@Test
	public void ooobcast() {
		assertFalse(ui.run("verify -input_mpi_nprocs=5", filename("ooobcast.c")));
	}

	@Test
	public void reduce() {
		assertTrue(ui.run("verify -input_mpi_nprocs=5", filename("reduce.c")));
	}

	@Test
	public void reduce_max() {
		assertTrue(ui.run("verify -input_mpi_nprocs=5", filename("reduce_max.c")));
	}

	@Test
	public void allreduce() {
		assertTrue(ui.run("verify -input_mpi_nprocs=5", filename("allreduce.c")));
	}

	@Test
	public void scatter() {
		assertTrue(ui.run("verify -input_mpi_nprocs=5", filename("scatter.c")));
	}

	@Test
	public void gather() {
		assertTrue(ui.run("verify -input_mpi_nprocs=5", filename("gather.c")));
	}

	@Test
	public void allgather() {
		assertTrue(ui.run("verify -input_mpi_nprocs=5", filename("allgather.c")));
	}

	@Test
	public void ooogather() {
		assertFalse(ui.run("verify -input_mpi_nprocs=5", filename("ooogather.c")));
	}

	@Test
	public void noninterference() {
		assertFalse(ui.run("verify -input_mpi_nprocs=2",
				filename("noninterference.c")));
	}

	@Test
	public void bcastgather1() {
		assertTrue(ui.run("verify -input_mpi_nprocs=5", filename("bcastgather1.c")));
	}
}
