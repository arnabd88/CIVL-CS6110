package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.civl.run.UserInterface;

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
		assertTrue(ui.run("verify", filename("adder.cvl"), "-inputB=5"));
	}

	@Test
	public void adder2() {
		assertTrue(ui.run("verify", filename("adder2.cvl"), "-inputN=4"));
	}

	@Test
	public void adderBad() {
		assertFalse(ui.run("verify", filename("adderBad.cvl"), "-inputB=4",
				"-min"));
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
		assertFalse(ui.run("replay", filename("barrierBad.cvl"), "-id=0"));
	}

	@Test
	public void blockAdder() {
		assertTrue(ui.run("verify", "-inputB=6", "-inputW=3",
				filename("blockAdder.cvl")));
	}

	@Test
	public void blockAdderBad() {
		assertFalse(ui.run("verify", "-inputB=6", "-inputW=3",
				filename("blockAdderBad.cvl"), "-min"));
		assertFalse(ui.run("replay", filename("blockAdderBad.cvl")));
	}

	@Test
	public void dining() {
		assertTrue(ui.run("verify", "-inputBOUND=4", filename("dining.cvl")));
	}

	@Test
	public void diningBad() {
		assertFalse(ui.run("verify", "-inputB=4", filename("diningBad.cvl"),
				"-min"));
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
	public void threadPrivate() {
		assertTrue(ui.run("verify", "-inputTHREADS_BOUND=2", "-inputN_BOUND=4",
				"-enablePrintf=false", filename("fig4.98-threadprivate.cvl")));
	}

	@Test
	public void waitSelf() {
		assertFalse(ui.run("verify", filename("waitSelf.cvl")));
	}
	
	@Test
	public void dlqueue() {
		assertTrue(ui.run("verify", filename("dlqueue.cvl")));
	}

}
