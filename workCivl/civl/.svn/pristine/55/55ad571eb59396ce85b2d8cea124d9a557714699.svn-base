package edu.udel.cis.vsl.civl.run.IF;

import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.seedO;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;

import edu.udel.cis.vsl.abc.preproc.IF.Preprocessor;
import edu.udel.cis.vsl.civl.config.IF.CIVLConstants;
import edu.udel.cis.vsl.civl.log.IF.CIVLExecutionException;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.semantics.IF.Transition;
import edu.udel.cis.vsl.civl.semantics.IF.TransitionSequence;
import edu.udel.cis.vsl.civl.state.IF.CIVLStateException;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.gmc.CommandLineException;
import edu.udel.cis.vsl.gmc.GMCConfiguration;
import edu.udel.cis.vsl.gmc.GuidedTransitionChooser;
import edu.udel.cis.vsl.gmc.MisguidedExecutionException;
import edu.udel.cis.vsl.gmc.RandomTransitionChooser;
import edu.udel.cis.vsl.gmc.Replayer;
import edu.udel.cis.vsl.gmc.Trace;
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
			Model model, File traceFile, PrintStream out, PrintStream err,
			Preprocessor preprocessor) throws CommandLineException,
			IOException, MisguidedExecutionException {
		TracePlayer result = new TracePlayer(config, model, out, err,
				preprocessor);
		GuidedTransitionChooser<State, Transition, TransitionSequence> guidedChooser = new GuidedTransitionChooser<>(
				result.enabler, traceFile);

		result.chooser = guidedChooser;
		result.replayer.setLength(guidedChooser.getLength());
		return result;
	}

	public static TracePlayer randomPlayer(GMCConfiguration config,
			Model model, PrintStream out, PrintStream err,
			Preprocessor preprocessor) throws CommandLineException,
			IOException, MisguidedExecutionException {
		TracePlayer result = new TracePlayer(config, model, out, err,
				preprocessor);
		String seedString = (String) config.getValue(seedO);
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
			PrintStream err, Preprocessor preprocessor)
			throws CommandLineException {
		super(config, model, out, err, preprocessor);
		// turn the following off because they duplicate what
		// the Replayer prints:
		// TODO check here
		// stateManager.setShowStates(false);
		// stateManager.setShowSavedStates(false);
		// civlConfig.setShowStates(false);
		civlConfig.setShowSavedStates(config
				.isTrue(CIVLConstants.showSavedStatesO));
		if (config.getValue(CIVLConstants.showTransitionsO) == null)
			civlConfig.setShowTransitions(true);
		civlConfig.setVerbose(false);
		log.setSearcher(null);
		replayer = new Replayer<State, Transition>(stateManager, out);
		replayer.setPrintAllStates(civlConfig.showStates()
				|| civlConfig.debugOrVerbose() || civlConfig.showSavedStates());
		replayer.setPredicate(predicate);
	}

	public TracePlayer(GMCConfiguration config, Model model,
			TransitionChooser<State, Transition> chooser, PrintStream out,
			PrintStream err, Preprocessor preprocessor)
			throws CommandLineException {
		this(config, model, out, err, preprocessor);
		this.chooser = chooser;
	}

	public TracePlayer(GMCConfiguration config, Model model, File traceFile,
			PrintStream out, PrintStream err, Preprocessor preprocessor)
			throws CommandLineException, IOException,
			MisguidedExecutionException {
		this(config, model, out, err, preprocessor);
		this.chooser = new GuidedTransitionChooser<State, Transition, TransitionSequence>(
				enabler, traceFile);
	}

	public Trace<Transition, State> run() throws MisguidedExecutionException {
		try {
			State initialState = stateFactory.initialState(model);
			Trace<Transition, State> trace = replayer.play(initialState,
					chooser, this.civlConfig.showTransitions())[0];
			boolean violation = trace.violation();

			violation = violation || log.numErrors() > 0;
			if (violation) {
				civlConfig.out().println("Violation(s) found.");
				civlConfig.out().flush();
			}
			trace.setViolation(violation);
			return trace;
		} catch (CIVLStateException stateException) {
			throw new CIVLExecutionException(stateException.kind(),
					stateException.certainty(), "",
					stateException.getMessage(),
					symbolicAnalyzer.stateToString(stateException.state()),
					stateException.source());
		}
	}

	public void printStats() {
		civlConfig.out().print("   statesInstantiated  : ");
		civlConfig.out().println(stateManager.getNumStateInstances());
		civlConfig.out().print("   statesSaved         : ");
		civlConfig.out().println(stateManager.getNumStatesSaved());
		civlConfig.out().println(
				"   maxProcs            : " + stateManager.maxProcs());
		if (isRandom)
			civlConfig.out().println("   seed                : " + seed);

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
