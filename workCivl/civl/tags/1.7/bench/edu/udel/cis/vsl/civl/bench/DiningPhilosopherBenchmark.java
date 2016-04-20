package edu.udel.cis.vsl.civl.bench;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

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
		String civlDir = ".";

		if (args.length > 0)
			civlDir = args[0];
		System.out.println(">>>>>>>> Dining philosopher <<<<<<<<");
		ui.run("verify -echo -inputBOUND=9 " + civlDir
				+ "/examples/concurrency/dining.cvl");
	}

}
