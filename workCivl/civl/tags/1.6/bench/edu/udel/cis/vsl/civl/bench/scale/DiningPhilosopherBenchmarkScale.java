package edu.udel.cis.vsl.civl.bench.scale;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

/**
 * Benchmark of the dining philosopher example. Execution time should be within
 * 20 to 58 seconds.
 * 
 * @author zmanchun
 * 
 */
public class DiningPhilosopherBenchmarkScale {
	private static UserInterface ui = new UserInterface();

	public static void main(String[] args) {
		String civlDir = ".";

		if (args.length > 0)
			civlDir = args[0];
		for (int i = 2; i <= 10; i++) {
			System.out.println(">>>>>>>> Dining philosopher <<<<<<<<");
			ui.run("verify -inputBOUND=" + i + " " + civlDir
					+ "/examples/concurrency/dining.cvl");
		}
	}

}
