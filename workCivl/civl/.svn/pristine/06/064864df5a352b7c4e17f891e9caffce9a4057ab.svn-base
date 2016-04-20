package edu.udel.cis.vsl.civl.bench.scale;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

/**
 * Benchmark of the barrier example. Execution time should be within 20 to 58
 * seconds.
 * 
 * @author zmanchun
 * 
 */
public class BarrierBenchmarkScale {
	private static UserInterface ui = new UserInterface();

	public static void main(String[] args) {
		String civlDir = ".";

		if (args.length > 0)
			civlDir = args[0];
		for (int i = 2; i <= 8; i++) {
			System.out.println(">>>>>>>> Barrier <<<<<<<<");
			ui.run("verify -echo -inputB=" + i + " " + civlDir
					+ "/examples/concurrency/barrier.cvl");
		}
	}

}
