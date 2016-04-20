package edu.udel.cis.vsl.civl.bench;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

/**
 * Benchmark of the barrier example. Execution time should be within 20 to 58
 * seconds.
 * 
 * @author zmanchun
 * 
 */
public class BarrierBenchmark {
	private static UserInterface ui = new UserInterface();

	public static void main(String[] args) {
		// -inputB=7: 26 seconds
		String civlDir = ".";

		if (args.length > 0)
			civlDir = args[0];
		System.out.println(">>>>>>>> Barrier <<<<<<<<");
		ui.run("verify -echo -inputB=7 " + civlDir
				+ "/examples/concurrency/barrier.cvl");
	}

}
