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
		ui.run("verify -echo -inputB=10 -inputW=4 examples/concurrency/blockAdder.cvl");
	}

}
