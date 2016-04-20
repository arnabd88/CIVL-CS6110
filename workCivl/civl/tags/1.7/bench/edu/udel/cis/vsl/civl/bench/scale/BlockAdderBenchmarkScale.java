package edu.udel.cis.vsl.civl.bench.scale;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

/**
 * Benchmark of the block adder example. Execution time should be within 20 to
 * 58 seconds.
 * 
 * @author zmanchun
 * 
 */
public class BlockAdderBenchmarkScale {
	private static UserInterface ui = new UserInterface();

	public static void main(String[] args) {
		String civlDir = ".";

		if (args.length > 0)
			civlDir = args[0];
		for (int i = 2; i <= 11; i++) {
			System.out.println(">>>>>>>> Block adder <<<<<<<<");
			ui.run("verify -inputB=" + 2 * i + " -inputW=" + i + " "
					+ civlDir + "/examples/concurrency/blockAdder.cvl");
		}
	}

}
