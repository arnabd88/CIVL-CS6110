package edu.udel.cis.vsl.civl.bench;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

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
		String civlDir = ".";

		if (args.length > 0)
			civlDir = args[0];
		System.out.println(">>>>>>>> Adder <<<<<<<<");
		ui.run("verify -echo -inputB=8 " + civlDir
				+ "/examples/concurrency/adder.cvl");
	}

}
