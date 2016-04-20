package edu.udel.cis.vsl.civl;

import edu.udel.cis.vsl.civl.run.UserInterface;

/**
 * Benchmark of the dining philosopher example. Execution time should be within
 * 20 to 58 seconds.
 * 
 * @author zmanchun
 * 
 */
public class DiningPhilosopherBenchmark {
	private static UserInterface ui = new UserInterface();

	public static void main(String[] args) {
		// -inputB=9: 19 seconds
		// -inputB=10: 56 seconds
		ui.run("verify -inputB=9 examples/concurrency/dining.cvl");
	}

}
