package edu.udel.cis.vsl.civl.bench;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

/**
 * Benchmark of the message passing example. Execution time should be within 20
 * to 58 seconds.
 * 
 * @author zmanchun
 * 
 */
public class MessagePassingBenchmark {
	private static UserInterface ui = new UserInterface();

	public static void main(String[] args) {
		// no longer appears to be a serious benchmark, executes too quickly
		String civlDir = ".";

		if (args.length > 0)
			civlDir = args[0];
		System.out.println(">>>>>>>> Adder <<<<<<<<");
		ui.run("verify  -input_NPROCS=4 -inputnsteps=2 -inputnx=2 -inputny=2 "
				+ "-inputNPROCSX=2 -inputNPROCSY=2 -enablePrintf=false "
				+ civlDir + "/examples/mpi/diffusion2d.c");
	}

}
