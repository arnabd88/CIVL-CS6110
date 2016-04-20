package edu.udel.cis.vsl.civl.run.IF;

import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.collectOutputO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.maxdepthO;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.channels.FileChannel;
import java.nio.channels.FileLock;
import java.util.Map;
import java.util.Set;

import edu.udel.cis.vsl.civl.config.IF.CIVLConstants;
import edu.udel.cis.vsl.civl.log.IF.CIVLExecutionException;
import edu.udel.cis.vsl.civl.log.IF.CIVLLogEntry;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.predicate.IF.Predicates;
import edu.udel.cis.vsl.civl.run.common.VerificationStatus;
import edu.udel.cis.vsl.civl.semantics.IF.Transition;
import edu.udel.cis.vsl.civl.semantics.IF.TransitionSequence;
import edu.udel.cis.vsl.civl.state.IF.CIVLStateException;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.civl.util.IF.Printable;
import edu.udel.cis.vsl.gmc.CommandLineException;
import edu.udel.cis.vsl.gmc.DfsSearcher;
import edu.udel.cis.vsl.gmc.ExcessiveErrorException;
import edu.udel.cis.vsl.gmc.GMCConfiguration;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

public class Verifier extends Player {

	private String errorBoundExceeds;

	VerificationStatus verificationStatus;

	class SearchUpdater implements Printable {
		@Override
		public void print(PrintStream out) {
			long time = (long) Math
					.ceil((System.currentTimeMillis() - startTime) / 1000.0);
			long megabytes = (long) (((double) Runtime.getRuntime()
					.totalMemory()) / (double) 1048576.0);

			out.print(time + "s: ");
			out.print("mem=" + megabytes + "Mb");
			out.print(" trans=" + executor.getNumSteps());
			out.print(" traceSteps=" + searcher.numTransitions());
			out.print(" explored=" + stateManager.numStatesExplored());
			out.print(" saved=" + stateManager.getNumStatesSaved());
			out.print(" prove=" + modelFactory.universe().numProverValidCalls());
			out.println();
		}
	}

	/**
	 * Updater for the web app. Instead of printing to the given stream, it
	 * ignores that stream and instead creates a new file and prints the data to
	 * that file.
	 * 
	 * @author siegel
	 *
	 */
	class WebUpdater implements Printable {

		/**
		 * String used to form the name of the file that will be created. This
		 * string will have the time step appended to it to create a unique
		 * file.
		 */
		private String filenameRoot;

		/**
		 * The directory in which the new file will be created.
		 */
		private File directory;

		/**
		 * The number of times {@link #print(PrintStream)} has been called on
		 * this updater.
		 */
		private int timeStep = 0;

		public WebUpdater(File directory, String filenameRoot) {
			this.directory = directory;
			this.filenameRoot = filenameRoot;
		}

		private void fail(File file, String msg) {
			throw new CIVLInternalException(msg + " " + file.getAbsolutePath(),
					(CIVLSource) null);
		}

		private void print(boolean isFinal) {
			double time = Math
					.ceil((System.currentTimeMillis() - startTime) / 100.0) / 10.0;
			long megabytes = (long) (((double) Runtime.getRuntime()
					.totalMemory()) / (double) 1048576.0);
			File file;

			timeStep++;
			file = new File(directory, filenameRoot + "_" + timeStep + ".txt");
			try {
				if (file.exists())
					file.delete();
				file.createNewFile();

				FileOutputStream stream = new FileOutputStream(file);
				FileChannel channel = stream.getChannel();
				FileLock lock = channel.lock();
				PrintStream out = new PrintStream(stream);

				out.println("{");
				out.println("\"time\" : " + time + " ,");
				out.println("\"mem\" : " + megabytes + " ,");
				out.println("\"steps\" : " + searcher.numTransitions() + " ,");
				out.println("\"trans\" : " + executor.getNumSteps() + " ,");
				out.println("\"seen\" : " + searcher.numStatesSeen() + " ,");
				out.println("\"saved\" : " + stateManager.getNumStatesSaved()
						+ " ,");
				out.println("\"prove\" : "
						+ modelFactory.universe().numProverValidCalls() + " ,");
				out.println("\"counterexample\" : "
						+ log.getMinimalCounterexampleSize() + ",");
				out.println("\"isFinal\" : " + isFinal);
				out.println("}");
				out.flush();
				lock.release();
				out.close();
			} catch (IOException e) {
				fail(file, "Could not write to file");
			}
		}

		@Override
		public void print(PrintStream out) {
			print(false);
		}

		public void printFinal() {
			print(true);
		}
	}

	/**
	 * Runnable to be used to create a thread that every so many seconds tells
	 * the state manager to print an update message.
	 * 
	 * @author siegel
	 * 
	 */
	class UpdaterRunnable implements Runnable {

		/**
		 * Number of milliseconds between sending update message to state
		 * manager.
		 */
		private long millis;

		/**
		 * Constructs new runnable with given number of milliseconds.
		 * 
		 * @param millis
		 *            number of milliseconds between update messages
		 */
		public UpdaterRunnable(long millis) {
			this.millis = millis;
		}

		/**
		 * Runs this thread. The thread will loop forever until interrupted,
		 * then it will terminate.
		 */
		@Override
		public void run() {
			while (alive) {
				try {
					Thread.sleep(millis);
					stateManager.printUpdate();
				} catch (InterruptedException e) {
				}
			}
		}
	}

	/**
	 * Should the update thread run?
	 */
	private volatile boolean alive = true;

	/**
	 * Number of seconds between printing updates.
	 */
	private int updatePeriod;

	/**
	 * The object used to print the update message.
	 */
	private Printable updater;

	/**
	 * The update thread itself.
	 */
	private Thread updateThread = null;

	/**
	 * The object used to perform the depth-first search of the state space.
	 * 
	 */
	private DfsSearcher<State, Transition, TransitionSequence> searcher;

	// private boolean shortFileNamesShown;

	/**
	 * The time at which execution started, as a double.
	 */
	private double startTime;

	public Verifier(
			GMCConfiguration config,
			Model model,
			PrintStream out,
			PrintStream err,
			double startTime,
			boolean collectOutputs,
			String[] outputNames,
			Map<BooleanExpression, Set<Pair<State, SymbolicExpression[]>>> specOutputs)
			throws CommandLineException {
		super(config, model, out, err, collectOutputs);
		if (random) {
			throw new CommandLineException(
					"\"-random\" mode is incompatible with civl verify command.");
		}
		this.startTime = startTime;
		if (outputNames != null && specOutputs != null)
			this.addPredicate(Predicates.newFunctionalEquivalence(
					modelFactory.universe(), symbolicAnalyzer, outputNames,
					specOutputs));
		searcher = new DfsSearcher<State, Transition, TransitionSequence>(
				enabler, stateManager, predicate);
		if (civlConfig.debug())
			searcher.setDebugOut(out);
		searcher.setName(sessionName);
		log.setSearcher(searcher);
		if (minimize)
			log.setMinimize(true);
		if (config.getAnonymousSection().getValue(maxdepthO) != null)
			searcher.boundDepth(maxdepth);
		if (config.getAnonymousSection().isTrue(CIVLConstants.webO)) {
			updatePeriod = CIVLConstants.webUpdatePeriod;
			updater = new WebUpdater(new File(CIVLConstants.CIVLREP), "update");
		} else {
			updatePeriod = CIVLConstants.consoleUpdatePeriod;
			updater = new SearchUpdater();
		}
		stateManager.setUpdater(updater);
		errorBoundExceeds = "errorBoundExceeds";
		// this.shortFileNamesShown = shortFileNamesShown;
		this.errorBoundExceeds = "Terminating search after finding "
				+ this.log.errorBound() + " violation";
		if (log.errorBound() > 1)
			errorBoundExceeds += "s";
		errorBoundExceeds += ".";
	}

	public Verifier(GMCConfiguration config, Model model, PrintStream out,
			PrintStream err, double startTime, boolean collectOutputs)
			throws CommandLineException {
		this(config, model, out, err, startTime, collectOutputs, null, null);
	}

	public Verifier(
			GMCConfiguration config,
			Model model,
			PrintStream out,
			PrintStream err,
			double startTime,
			String[] outputNames,
			Map<BooleanExpression, Set<Pair<State, SymbolicExpression[]>>> specOutputs)
			throws CommandLineException {
		this(config, model, out, err, startTime, false, outputNames,
				specOutputs);
	}

	public Verifier(GMCConfiguration config, Model model, PrintStream out,
			PrintStream err, double startTime) throws CommandLineException {
		this(config, model, out, err, startTime, config.getAnonymousSection()
				.isTrue(collectOutputO), null, null);
	}

	/**
	 * Prints only those metrics specific to this Verifier. General metrics,
	 * including time, memory, symbolic expressions, etc., are dealt with in the
	 * general UserInterface class.
	 */
	public void printStats() {
		civlConfig.out().print("   max process count   : ");
		civlConfig.out().println(stateManager.maxProcs());
		civlConfig.out().print("   states              : ");
		civlConfig.out().println(stateManager.numStatesExplored());
		civlConfig.out().print("   states saved        : ");
		civlConfig.out().println(stateManager.getNumStatesSaved());
		// civlConfig.out().print("   statesSeen        : ");
		// civlConfig.out().println(searcher.numStatesSeen());
		civlConfig.out().print("   state matches       : ");
		civlConfig.out().println(searcher.numStatesMatched());
		civlConfig.out().print("   transitions         : ");
		civlConfig.out().println(executor.getNumSteps());
		civlConfig.out().print("   trace steps         : ");
		civlConfig.out().println(searcher.numTransitions());
	}

	public boolean run() throws FileNotFoundException {
		try {
			State initialState = stateFactory.initialState(model);
			boolean violationFound = false;

			updateThread = new Thread(new UpdaterRunnable(updatePeriod * 1000));
			updateThread.start();
			if (civlConfig.debugOrVerbose() || civlConfig.showStates()) {
				civlConfig.out().println();
				// stateFactory.printState(out, initialState);
				civlConfig.out().print(
						symbolicAnalyzer.stateInformation(initialState));
				// initialState.print(out);
			}
			try {
				while (true) {
					boolean workRemains;

					if (violationFound) {
						// may throw ExcessiveErrorException...
						workRemains = searcher.proceedToNewState() ? searcher
								.search() : false;
					} else {
						// may throw ExcessiveErrorException...
						workRemains = searcher.search(initialState);
					}
					if (!workRemains)
						break;
					violationFound = true;

					CIVLLogEntry entry = new CIVLLogEntry(config,
							this.predicate.getUnreportedViolation());

					log.report(entry); // may throw ExcessiveErrorException
				}
			} catch (ExcessiveErrorException e) {
				violationFound = true;
				civlConfig.out().println(errorBoundExceeds);
			}
			terminateUpdater();
			if (violationFound || log.numEntries() > 0) {
				result = "The program MAY NOT be correct.  See "
						+ log.getLogFile();
				try {
					log.save();
				} catch (FileNotFoundException e) {
					System.err.println("Failed to print log file "
							+ log.getLogFile());
				}
			} else {
				result = "The standard properties hold for all executions.";
				// result = "No violations found.";
			}
			this.verificationStatus = new VerificationStatus(
					stateManager.maxProcs(), stateManager.numStatesExplored(),
					stateManager.getNumStatesSaved(),
					searcher.numStatesMatched(), executor.getNumSteps(),
					searcher.numTransitions());
			return !violationFound && log.numEntries() == 0;
		} catch (CIVLStateException stateException) {
			throw new CIVLExecutionException(stateException.kind(),
					stateException.certainty(), "",
					stateException.getMessage(),
					symbolicAnalyzer.stateInformation(stateException.state()),
					stateException.source());
		}

	}

	/**
	 * Terminates the update thread. This will be called automatically if
	 * control exits normally from {@link #run()}, but if an exception is thrown
	 * and caught elsewhere, this method should be called.
	 */
	public void terminateUpdater() {
		alive = false;
		if (updateThread != null)
			updateThread.interrupt();
		updateThread = null;
		if (civlConfig.web()) {
			// last update with final stats needed for web page...
			((WebUpdater) updater).printFinal();
		}
	}
}
