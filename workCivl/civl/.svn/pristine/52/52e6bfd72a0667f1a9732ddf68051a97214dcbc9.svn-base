package edu.udel.cis.vsl.civl.run;

import java.io.FileNotFoundException;
import java.io.PrintStream;

import edu.udel.cis.vsl.civl.log.CIVLLogEntry;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.state.State;
import edu.udel.cis.vsl.civl.transition.Transition;
import edu.udel.cis.vsl.civl.transition.TransitionSequence;
import edu.udel.cis.vsl.gmc.CommandLineException;
import edu.udel.cis.vsl.gmc.DfsSearcher;
import edu.udel.cis.vsl.gmc.ExcessiveErrorException;
import edu.udel.cis.vsl.gmc.GMCConfiguration;

public class Verifier extends Player {

	private DfsSearcher<State, Transition, TransitionSequence> searcher;

	public Verifier(GMCConfiguration config, Model model, PrintStream out)
			throws CommandLineException {
		super(config, model, out);
		searcher = new DfsSearcher<State, Transition, TransitionSequence>(
				enabler, stateManager, predicate);
		if (debug)
			searcher.setDebugOut(out);
		searcher.setName(sessionName);
		log.setSearcher(searcher);
		if (minimize)
			log.setMinimize(true);
		if (config.getValue(UserInterface.maxdepthO) != null)
			searcher.boundDepth(maxdepth);
	}

	/**
	 * Prints only those metrics specific to this Verifier. General metrics,
	 * including time, memory, symbolic expressions, etc., are dealt with in the
	 * general UserInterface class.
	 */
	public void printStats() {
		out.print("   maxProcs            : ");
		out.println(stateManager.maxProcs());
		out.print("   statesInstantiated  : ");
		out.println(stateManager.getNumStateInstances());
		out.print("   statesSaved         : ");
		out.println(stateManager.getNumStatesSaved());
		out.print("   statesSeen          : ");
		out.println(searcher.numStatesSeen());
		out.print("   statesMatched       : ");
		out.println(searcher.numStatesMatched());
		out.print("   transitions         : ");
		out.println(searcher.numTransitions());
	}

	public boolean run() {
		State initialState = stateFactory.initialState(model);
		boolean violationFound = false;

		try {
			while (true) {
				boolean workRemains;

				if (violationFound)
					workRemains = searcher.proceedToNewState() ? searcher
							.search() : false;
				else
					workRemains = searcher.search(initialState);
				if (!workRemains)
					break;
				log.report(new CIVLLogEntry(config, predicate.getViolation()));
				violationFound = true;
			}
		} catch (ExcessiveErrorException e) {
			violationFound = true;
			out.println("Error bound exceeded: search terminated");
		} catch (Exception e) {
			violationFound = true;
			out.println(e);
			e.printStackTrace(out);
			out.println();
		}
		if (violationFound || log.numEntries() > 0) {
			result = "The program MAY NOT be correct.  See " + log.getLogFile();
			try {
				log.save();
			} catch (FileNotFoundException e) {
				System.err.println("Failed to print log file "
						+ log.getLogFile());
			}
		} else {
			result = "The standard properties hold for all executions.";
		}
		return !violationFound && log.numEntries() == 0;
	}
}
