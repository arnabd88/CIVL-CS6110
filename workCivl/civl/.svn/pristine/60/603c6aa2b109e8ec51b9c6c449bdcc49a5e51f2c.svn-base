package edu.udel.cis.vsl.civl;

import edu.udel.cis.vsl.civl.run.UserInterface;

/**
 * Benchmark of the adder example. Execution time should be within 20 to 58
 * seconds.
 * 
 * @author zmanchun
 * 
 */
public class AdderBenchmark {
	private static UserInterface ui = new UserInterface();

	public static void main(String[] args) {
		// -inputB=7: 12 seconds
		// -inputB=8: 39 seconds
		ui.run("verify -inputB=8 examples/concurrency/adder.cvl");
	}

}
