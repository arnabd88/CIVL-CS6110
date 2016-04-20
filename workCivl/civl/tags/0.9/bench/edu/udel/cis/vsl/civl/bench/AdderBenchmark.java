package edu.udel.cis.vsl.civl.bench;

import edu.udel.cis.vsl.civl.run.UserInterface;

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
		ui.run("verify -echo -inputB=8 examples/concurrency/adder.cvl");
		
		/*
		 *Result of new POR
		 *
maurice:CIVL zmanchun$ civl verify -inputB=8 -por=new examples/concurrency/adder.cvl
CIVL v0.6 of 2014-02-01 -- http://vsl.cis.udel.edu/civl

=================== Stats ===================
   validCalls          : 33810
   proverCalls         : 42
   memory (bytes)      : 369098752
   time (s)            : 9.13
   maxProcs            : 9
   statesInstantiated  : 47021
   statesSaved         : 8840
   statesSeen          : 8824
   statesMatched       : 1291
   steps               : 12520
   transitions         : 10114
		 *
maurice:CIVL zmanchun$ civl verify -inputB=10 -por=new examples/concurrency/adder.cvl

CIVL v0.6 of 2014-02-01 -- http://vsl.cis.udel.edu/civl
17s: mem=237Mb steps=18391 trans=14999 seen=12876 saved=12886 prove=52
32s: mem=324Mb steps=41128 trans=33599 seen=28708 saved=28719 prove=52

=================== Stats ===================
   validCalls          : 165242
   proverCalls         : 52
   memory (bytes)      : 239075328
   time (s)            : 41.2
   maxProcs            : 11
   statesInstantiated  : 230673
   statesSaved         : 43196
   statesSeen          : 43176
   statesMatched       : 7181
   steps               : 61755
   transitions         : 50356

		 */
	}

}
