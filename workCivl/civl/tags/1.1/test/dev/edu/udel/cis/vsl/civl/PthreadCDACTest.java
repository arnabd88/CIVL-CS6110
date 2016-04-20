package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Ignore;
import org.junit.Test;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class PthreadCDACTest {
	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples", "pthread"),
			"CDAC");

	private static UserInterface ui = new UserInterface();
	
	/* *************************** Helper Methods *************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}
	
	/* **************************** Test Methods *************************** */

	// Yes
	// None
	@Ignore
	@Test
	public void pthread_demo_datarace() throws ABCException {
		assertTrue(ui.run("verify", filename("pthread-demo-datarace.c") ));
	}
	
	@Test
	public void pthread_finding_k_matches() throws ABCException {
		assertTrue(ui.run("verify", "-inputCIVL_argc=3", "-errorBound=2", filename("pthread-finding-k-matches.c") ));
	}

	@Test
	public void pthread_findminimumvalue() throws ABCException {
		assertTrue(ui.run("verify", filename("pthread-findminimumvalue.c") ));
	}
	
	@Test
	public void pthread_infinitynorm_colwise() throws ABCException {
		assertTrue(ui.run("verify", filename("pthread-infinitynorm-colwise.c") ));
	}
	
	@Test
	public void pthread_infinitynorm_rowwise() throws ABCException {
		assertTrue(ui.run("verify", filename("pthread-infinitynorm-rowwise.c") ));
	}
	
	@Test
	public void pthread_jacobi() throws ABCException {
		assertTrue(ui.run("verify", "-inputCIVL_argc=3", filename("pthread-jacobi.c") ));
	}
	
	@Test
	public void pthread_loop_carried() throws ABCException {
		assertTrue(ui.run("verify", filename("pthread-loop-carried.c") ));
	}
	
	@Test
	public void pthread_numerical_integration() throws ABCException {
		assertTrue(ui.run("verify", filename("pthread-numerical-integration.c") ));
	}
	
	@Test
	public void pthread_producer_consumer() throws ABCException {
		assertTrue(ui.run("verify", filename("pthread-producer-consumer.c") ));
	}
	
	@Test
	public void pthread_vectorvector_multi() throws ABCException {
		assertTrue(ui.run("verify", filename("pthread-vectorvector-multi.c") ));
	}
	
	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
