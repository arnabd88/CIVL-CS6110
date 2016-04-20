package edu.udel.cis.vsl.civl.bench.scale;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

/**
 * Benchmark of the message passing example. Execution time should be within 20
 * to 58 seconds.
 * 
 * @author zmanchun
 * 
 */
public class MessagePassingBenchmarkScale {
	private static UserInterface ui = new UserInterface();

	public static void main(String[] args) {
		String civlDir = ".";

		if (args.length > 0)
			civlDir = args[0];
		for (int nx = 2; nx < 4; nx++)
			for (int ny = 2; ny < 4; ny++) {
				System.out.println(">>>>>>>> Diffusion2d <<<<<<<<");
				ui.run("verify  " + "-input_NPROCS=" + nx * ny
						+ " -inputnsteps=2 -inputnx=2 -inputny=2 "
						+ "-inputNPROCSX=" + nx + " " + "-inputNPROCSY=" + ny
						+ " -enablePrintf=false " + civlDir
						+ "/examples/mpi/diffusion2d.c");
			}

	}

}
