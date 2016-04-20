package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class ConcurrencyTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "concurrency");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void adder() {
		assertTrue(ui.run("verify", "-inputB=5", filename("adder.cvl")));
	}

	@Test
	public void adder2() {
		assertTrue(ui.run("verify", "-inputN=4", filename("adder2.cvl")));
	}

	@Test
	public void adderBad() {
		assertFalse(ui.run("verify", "-inputB=4", "-min",
				filename("adderBad.cvl")));
		assertFalse(ui.run("replay", filename("adderBad.cvl")));
	}

	@Test
	public void bank() {
		assertTrue(ui.run("verify", "-inputNUM_ACCOUNTS=3",
				filename("bank.cvl")));
	}

	@Test
	public void barrier() {
		assertTrue(ui.run("verify", "-inputB=4", filename("barrier.cvl")));
	}

	@Test
	public void barrier2() {
		assertTrue(ui.run("verify", "-inputB=4", filename("barrier2.cvl")));
	}

	@Test
	public void barrierBad() {
		assertFalse(ui.run("verify", "-min", "-inputB=4",
				filename("barrierBad.cvl")));
		assertFalse(ui.run("replay", "-id=0", filename("barrierBad.cvl")));
	}

	@Test
	public void blockAdder() {
		assertTrue(ui.run("verify", "-inputB=6", "-inputW=3",
				filename("blockAdder.cvl")));
	}

	@Test
	public void blockAdderBad() {
		assertFalse(ui.run("verify", "-inputB=6", "-inputW=3", "-min",
				filename("blockAdderBad.cvl")));
		assertFalse(ui.run("replay", filename("blockAdderBad.cvl")));
	}

	@Test
	public void dining() {
		assertTrue(ui.run("verify", "-inputBOUND=4", filename("dining.cvl")));
	}

	@Test
	public void diningBad() {
		assertFalse(ui.run("verify", "-inputB=4", "-min",
				filename("diningBad.cvl")));
		assertFalse(ui.run("replay", filename("diningBad.cvl")));
	}

	@Test
	public void locksBad() {
		assertFalse(ui.run("verify", filename("locksBad.cvl")));
	}

	@Test
	public void locksBad10() {
		assertFalse(ui.run("verify", filename("locksBad10.cvl")));
	}

	@Test
	public void locksGood() {
		assertTrue(ui.run("verify", filename("locksGood.cvl")));
	}

	@Test
	public void spawn() {
		assertTrue(ui.run("verify", "-inputN=10", filename("spawn.cvl")));
	}

	@Test
	public void spawn2() {
		assertTrue(ui.run("verify", "-inputN=10", filename("spawn2.cvl")));
	}

	@Test
	public void spawnBad() {
		assertFalse(ui.run("verify", "-inputN=10", filename("spawnBad.cvl")));
	}

	@Test
	public void waitSelf() {
		assertFalse(ui.run("verify", filename("waitSelf.cvl")));
	}

	@Test
	public void dlqueue() {
		assertTrue(ui.run("verify", filename("dlqueue.cvl")));
	}

	@Test
	public void hybrid() {
		assertFalse(ui.run("verify", "-inputNPROCS=2 -showModel -debug=false",
				filename("hybrid.cvl")));
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
		assertTrue(ui.run("verify", "-deadlock=potential -inputNPROCS_BOUND=8",
				"-inputN_BOUND=4", filename("ring.cvl")));
	}

	@Test
	public void ring1Bad() {
		assertFalse(ui.run("verify", "-deadlock=potential -inputNPROCS=3",
				filename("ring1Bad.cvl")));
	}

	@Test
	public void ring1() {
		assertTrue(ui.run("verify", "-deadlock=potential -inputNPROCS=3",
				filename("ring1.cvl")));
	}

	@Test
	public void ring2() {
		assertTrue(ui.run("verify", "-deadlock=potential -inputNPROCS=3",
				filename("ring2.cvl")));
	}

	@Test
	public void ring2Bad() {
		assertFalse(ui.run("verify", "-deadlock=potential -inputNPROCS=3",
				filename("ring2Bad.cvl")));
	}

	@Test
	public void ring3() {
		assertTrue(ui.run("verify -deadlock=potential", filename("ring3.cvl")));
	}

	@Test
	public void ring3Bad() {
		assertFalse(ui.run("verify -deadlock=potential",
				filename("ring3Bad.cvl")));
	}

	@Test
	public void wildcard() {
		assertTrue(ui.run("verify", "-inputNPROCS=5", "-enablePrintf=false",
				filename("wildcard.cvl")));
	}

	@Test
	public void wildcardBad() {
		assertFalse(ui.run("verify", "-enablePrintf=false",
				filename("wildcardBad.c")));
		ui.run("replay", filename("wildcardBad.c"));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
