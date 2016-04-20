package edu.udel.cis.vsl.civl.run;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;

import edu.udel.cis.vsl.abc.preproc.IF.Preprocessor;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.transition.Transition;
import edu.udel.cis.vsl.civl.transition.TransitionSequence;
import edu.udel.cis.vsl.gmc.CommandLineException;
import edu.udel.cis.vsl.gmc.GMCConfiguration;
import edu.udel.cis.vsl.gmc.GuidedTransitionChooser;
import edu.udel.cis.vsl.gmc.MisguidedExecutionException;
import edu.udel.cis.vsl.gmc.RandomTransitionChooser;
import edu.udel.cis.vsl.gmc.Replayer;
import edu.udel.cis.vsl.gmc.TransitionChooser;

/**
 * A tool to replay a trace saved by a previous CIVL session.
 * 
 * NOTE: need to have the new options override the ones specified in the trace
 * file.
 * 
 * @author siegel
 * 
 */
public class TracePlayer extends Player {

	private TransitionChooser<State, Transition> chooser;

	private Replayer<State, Transition> replayer;

	private boolean isRandom = false;

	private long seed = 0;

	public static TracePlayer guidedPlayer(GMCConfiguration config,
			Model model, File traceFile, PrintStream out,
			Preprocessor preprocessor) throws CommandLineException,
			IOException, MisguidedExecutionException {
		TracePlayer result = new TracePlayer(config, model, out, preprocessor);
		GuidedTransitionChooser<State, Transition, TransitionSequence> guidedChooser = new GuidedTransitionChooser<>(
				result.enabler, traceFile);

		result.chooser = guidedChooser;
		result.replayer.setLength(guidedChooser.getLength());
		return result;
	}

	public static TracePlayer randomPlayer(GMCConfiguration config,
			Model model, PrintStream out, Preprocessor preprocessor)
			throws CommandLineException, IOException,
			MisguidedExecutionException {
		TracePlayer result = new TracePlayer(config, model, out, preprocessor);
		String seedString = (String) config.getValue(UserInterface.seedO);
		RandomTransitionChooser<State, Transition, TransitionSequence> chooser;

		if (seedString == null)
			chooser = new RandomTransitionChooser<>(result.enabler);
		else {
			long seed;

			try {
				seed = new Long(seedString);
			} catch (NumberFormatException e) {
				throw new CommandLineException(
						"Expected long value for seed, saw " + seedString);
			}
			chooser = new RandomTransitionChooser<>(result.enabler, seed);
		}
		result.seed = chooser.getSeed();
		result.isRandom = true;
		result.chooser = chooser;
		return result;
	}

	TracePlayer(GMCConfiguration config, Model model, PrintStream out,
			Preprocessor preprocessor) throws CommandLineException {
		super(config, model, out, preprocessor);
		// turn the following off because they duplicate what
		// the Replayer prints:
		// TODO check here
		stateManager.setShowStates(false);
		stateManager.setShowSavedStates(false);
		stateManager.setShowTransitions(showTransitions);
		stateManager.setVerbose(false);
		log.setSearcher(null);
		replayer = new Replayer<State, Transition>(stateManager, out);
		replayer.setPrintAllStates(showStates || verbose || debug
				|| showSavedStates);
		replayer.setPredicate(predicate);
	}

	public TracePlayer(GMCConfiguration config, Model model,
			TransitionChooser<State, Transition> chooser, PrintStream out,
			Preprocessor preprocessor) throws CommandLineException {
		this(config, model, out, preprocessor);
		this.chooser = chooser;
	}

	public TracePlayer(GMCConfiguration config, Model model, File traceFile,
			PrintStream out, Preprocessor preprocessor)
			throws CommandLineException, IOException,
			MisguidedExecutionException {
		this(config, model, out, preprocessor);
		this.chooser = new GuidedTransitionChooser<State, Transition, TransitionSequence>(
				enabler, traceFile);
	}

	public boolean run() throws MisguidedExecutionException {
		State initialState = stateFactory.initialState(model);
		boolean violation = replayer.play(initialState, chooser);

		violation = violation || log.numErrors() > 0;
		if (violation) {
			out.println("Violation(s) found.");
			out.flush();
		}
		return !violation;
	}

	public void replayForGui(ArrayList<State> states,
			ArrayList<Transition> transitions)
			throws MisguidedExecutionException {
		State initialState = stateFactory.initialState(model);

		states.add(initialState);
		replayer.playForUi(initialState, chooser, states, transitions);
	}

	public void printStats() {
		out.print("   statesInstantiated  : ");
		out.println(stateManager.getNumStateInstances());
		out.print("   statesSaved         : ");
		out.println(stateManager.getNumStatesSaved());
		out.println("   maxProcs            : " + stateManager.maxProcs());
		if (isRandom)
			out.println("   seed                : " + seed);

	}

	/**
	 * Returns the random seed if this is a random simulator, otherwise 0.
	 * 
	 * @return the random seed
	 */
	public long getSeed() {
		return seed;
	}

	public boolean isRandom() {
		return isRandom;
	}

}
