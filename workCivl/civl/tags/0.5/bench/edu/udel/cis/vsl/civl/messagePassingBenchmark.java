package edu.udel.cis.vsl.civl;

import edu.udel.cis.vsl.civl.run.UserInterface;

/**
 * Benchmark of the message passing example. Execution time should be within 20
 * to 58 seconds.
 * 
 * @author zmanchun
 * 
 */
public class messagePassingBenchmark {
	private static UserInterface ui = new UserInterface();

	public static void main(String[] args) {
		// -inputNPROCS=5 -simplify=false: 17 seconds
		// -inputNPROCS=6 -simplify=false: 68 seconds
		// since 6 processes take much more than 50 seconds, so choose 5
		// processes.
		ui.run("verify -inputNPROCS=5 -simplify=false examples/messagePassing/ring.cvl");
	}

}
