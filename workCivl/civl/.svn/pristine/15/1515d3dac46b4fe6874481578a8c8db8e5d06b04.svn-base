package edu.udel.cis.vsl.civl.bench.scale;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

/**
 * Benchmark of the adder example. Execution time should be within 20 to 58
 * seconds.
 * 
 * @author zmanchun
 * 
 */
public class AdderBenchmarkScale {
	private static UserInterface ui = new UserInterface();

	public static void main(String[] args) {
		String civlDir = ".";

		if (args.length > 0)
			civlDir = args[0];
		for (int i = 2; i <= 8; i++) {
			System.out.println(">>>>>>>> Adder <<<<<<<<");
			ui.run("verify -inputB=" + i + " " + civlDir
					+ "/examples/concurrency/adder.cvl");
		}
	}

}
