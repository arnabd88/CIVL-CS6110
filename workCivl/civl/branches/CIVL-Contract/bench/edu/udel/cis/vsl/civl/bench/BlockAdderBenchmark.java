package edu.udel.cis.vsl.civl.bench;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

/**
 * Benchmark of the block adder example. Execution time should be within 20 to
 * 58 seconds.
 * 
 * @author zmanchun
 * 
 */
public class BlockAdderBenchmark {
	private static UserInterface ui = new UserInterface();

	public static void main(String[] args) {
		// -inputB=10 -inputW=4: 27 seconds
		String civlDir = ".";

		if (args.length > 0)
			civlDir = args[0];
		System.out.println(">>>>>>>> Block adder <<<<<<<<");
		ui.run("verify -echo -inputB=10 -inputW=4 " + civlDir
				+ "/examples/concurrency/blockAdder.cvl");
	}

}
