package edu.udel.cis.vsl.civl.bench;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

/**
 * Benchmark of the message passing example. Execution time should be within 20
 * to 58 seconds.
 * 
 * @author zmanchun
 * 
 */
public class MessagePassingBenchmark {
	private static UserInterface ui = new UserInterface();

	public static void main(String[] args) {
		// no longer appears to be a serious benchmark, executes too quickly
		ui.run("verify -echo -inputNPROCS_BOUND=10 -inputN_BOUND=3 examples/concurrency/ring.cvl");
	}

}
