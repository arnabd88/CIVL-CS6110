package edu.udel.cis.vsl.gmc;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.Date;
import java.util.SortedMap;
import java.util.TreeMap;

/**
 * A log for recording errors and corresponding traces encountered during a
 * model checking run.
 * 
 * In the course of performing a search, various kinds of "errors" may be
 * encountered. These do not necessarily pause the search. They are not even
 * necessarily noticed by the searcher. Each application using this package is
 * free to determine what in an error is and how to report them. Typically, an
 * error occurs in the process of computing the enabled transitions at a state,
 * or in the process of executing a transition. Division by zero, null pointer
 * dereferences, and so on, are typical errors that should be logged and
 * reported.
 * 
 * This class provides a convenient mechanism for logging such as errors as the
 * search progresses. Many applications do not necessarily stop after the first
 * error is discovered, but instead take some corrective mechanism (like
 * constraining the path condition in symbolic execution) and proceed with the
 * search. Those applications can use this class to record the errors
 * encountered.
 * 
 * In addition to recording errors, this class provides a number of convenient
 * services: using information provided by the application, it can determine
 * when two errors are considered "equivalent" and therefore only one instance
 * needs to be reported; it can prioritize the errors so that the most important
 * are reported to the user first; it can associate a trace to each error and
 * save these in a file, so the user can later replay the trace associate to
 * each error discovered.
 * 
 * @author Stephen F. Siegel, University of Delaware
 * 
 */
public class ErrorLog {

	// Instance fields...

	/**
	 * The searcher performing the search. May be null, in which case traces
	 * won't be saved, etc.
	 */
	private DfsSearcher<?, ?, ?> searcher;

	/**
	 * A canonical map used for storing and flyweighting the reported errors.
	 * Key=value for all entries in this map.
	 */
	private SortedMap<LogEntry, LogEntry> entryMap;

	/**
	 * Directory in which the log and trace files will be stored.
	 */
	private File directory;

	/**
	 * Name of the session: this name will be used to form the file name of all
	 * files created by this log.
	 */
	private String sessionName;

	/**
	 * Time and date at which this log was created.
	 */
	private Date date;

	/**
	 * The total number of errors reported to this log. This may be greater than
	 * the number stored by this log, because many of the errors reported may be
	 * equivalent, and only one from each equivalence class is stored.
	 */
	private int numErrors = 0;

	/**
	 * Total number of errors that can be reported before this log throws an
	 * {@link ExcessiveErrorException}.
	 */
	private int errorBound = 5;

	/**
	 * The size of the minimal counterexample (violation) logged so far, or -1
	 * if none has been logged.
	 */
	private int minimalCounterexampleSize = -1;

	/**
	 * Was this search truncated due to an excessive error exception?
	 */
	private boolean searchTruncated = false;

	/**
	 * The stream to which errors should be printed when they are logged.
	 * Typical applications want to report errors as soon as they are
	 * discovered, but continue with the search, and then also save the log of
	 * these errors.
	 */
	private PrintStream out;

	/**
	 * The file to which this log will be printed (in human-readable form) at
	 * the end.
	 */
	private File logFile;

	/**
	 * Search for a minimal counterexample?
	 */
	private boolean minimize;

	/**
	 * Creates new ErrorLog.
	 * 
	 * @param directory
	 *            the directory in which traces and the log file will be stored
	 * @param sessionName
	 *            the name to use for this session; it will form the root of the
	 *            names of all the files created
	 * @param out
	 *            the stream to which errors should be printed when they are
	 *            reported to this log
	 */
	public ErrorLog(File directory, String sessionName, PrintStream out) {
		this.out = out;
		if (!directory.exists()) {
			directory.mkdir();
		}
		if (!directory.isDirectory())
			throw new IllegalArgumentException("No directory named "
					+ directory);
		if (sessionName == null)
			throw new IllegalArgumentException("Session name is null");
		this.directory = directory;
		this.sessionName = sessionName;
		this.entryMap = new TreeMap<>();
		this.date = new Date();
		this.logFile = new File(directory, sessionName + "_log.txt");
	}

	// Helper methods...

	/**
	 * The name to use for the trace file, for the error of ID i reported to
	 * this log.
	 * 
	 * @param i
	 *            an integer
	 * @return a file name formed from the seesion name and the number i
	 */
	private String traceFileName(int i) {
		return sessionName + "_" + i + ".trace";
	}

	/**
	 * Returns the java File object corresponding to a file with name
	 * traceFileName(i) in the log directory. This does not create such a file,
	 * it merely constructs and returns the Java platform-independent
	 * representation of the file name as a File object.
	 * 
	 * @param i
	 *            an integer
	 * @return a File in the directory whose name is formed from the session
	 *         name and the number i
	 */
	private File traceFile(int i) {
		return new File(directory, traceFileName(i));
	}

	// Public methods...

	/**
	 * Are we searching for a minimal counterexample?
	 * 
	 * @return value of minimize flag
	 */
	public boolean getMinimize() {
		return minimize;
	}

	/**
	 * Sets the minimize flag to given value. If true, each time a violation is
	 * found, the search depth will be restricted to its current depth minus
	 * one.
	 * 
	 * @param value
	 *            true iff we want to search for a minimal counterexample
	 */
	public void setMinimize(boolean value) {
		this.minimize = value;
		searcher.boundDepth(Integer.MAX_VALUE);
		searcher.setMinimize(value);
	}

	/**
	 * Returns the directory in which trace files and the log will be stored.
	 * 
	 * @return the directory associated to this log
	 */
	public File getDirectory() {
		return directory;
	}

	public File getLogFile() {
		return logFile;
	}

	public void save() throws FileNotFoundException {
		PrintStream stream = new PrintStream(new FileOutputStream(logFile));

		print(stream);
		stream.close();
	}

	public void setSearcher(DfsSearcher<?, ?, ?> searcher) {
		this.searcher = searcher;
	}

	public DfsSearcher<?, ?, ?> searcher() {
		return searcher;
	}

	public int errorBound() {
		return errorBound;
	}

	public void setErrorBound(int value) {
		this.errorBound = value;
	}

	public int numErrors() {
		return numErrors;
	}

	public int numEntries() {
		return entryMap.size();
	}

	public void print(PrintStream out) {
		out.println("Session name....... " + sessionName);
		out.println("Directory.......... " + directory);
		out.println("Date............... " + date);
		out.println("numErrors.......... " + numErrors);
		out.println("numDistinctErrors.. " + entryMap.size());
		out.println("search truncated... " + searchTruncated);
		out.println();
		for (LogEntry entry : entryMap.values()) {
			entry.print(out);
			out.println();
		}
	}

	private void writeTraceFile(LogEntry entry) throws FileNotFoundException {
		File file = entry.getTraceFile();
		PrintStream out = new PrintStream(file);

		out.println("Session name....... " + sessionName);
		out.println("Directory.......... " + directory);
		out.println("Date............... " + date);
		out.println("Trace ID........... " + entry.getId());
		out.println("Violation number....... " + numErrors);
		out.println();
		out.println("== Begin Violation Message == ");
		entry.print(out);
		out.println("== End Violation Message == ");
		out.println();
		out.println("== Begin Configuration ==");
		entry.getConfiguration().print(out);
		out.println("== End Configuration ==");
		out.println();
		out.println("== Begin Trace ==");
		searcher.writeStack(out);
		out.println("== End Trace ==");
		out.flush();
		out.close();
	}

	/**
	 * 
	 * @param entry
	 * @throws FileNotFoundException
	 * @throws ExcessiveErrorException
	 *             if the number of errors reported has exceeded the specified
	 *             bound
	 */
	private void reportWithSearcher(LogEntry entry)
			throws FileNotFoundException {
		boolean isQuiet = entry.getConfiguration().isQuiet();
		int length = searcher.stack().size();
		LogEntry oldEntry = entryMap.get(entry);

		if (minimalCounterexampleSize < 0 || length < minimalCounterexampleSize) {
			minimalCounterexampleSize = length;
		}
		if(!isQuiet){
			out.println("\nViolation " + numErrors + " encountered at depth " + length
					+ ":");
			entry.printBody(out);
		}
		if (oldEntry != null) {
			int id = oldEntry.getId();
			File file = oldEntry.getTraceFile();
			int oldLength = oldEntry.getLength();
			if(!isQuiet){
				out.println("New log entry is equivalent to previously encountered entry "
						+ id);
			}
			if (length < oldLength) {
				if(!isQuiet){
					out.println("Length of new trace (" + length
							+ ") is less than length of old (" + oldLength
							+ "): replacing old with new...");
				}
				entry.setId(id);
				entry.setSize(length);
				entry.setTraceFile(file);
				entryMap.remove(entry);
				entryMap.put(entry, entry);
				file.delete();
				writeTraceFile(entry);
			} else {
				if(!isQuiet){
					out.println("Length of new trace (" + length
							+ ") is greater than or equal to length of old ("
							+ oldLength + "): ignoring new trace.");
				}
			}
		} else {
			int id = entryMap.size();
			File file = traceFile(id);
			if(!isQuiet){
				out.println("Logging new entry " + id + ", writing trace to "
						+ file);
			}
			entry.setTraceFile(file);
			entry.setId(id);
			entry.setSize(length);
			entryMap.put(entry, entry);
			writeTraceFile(entry);
		}
		numErrors++;
		if (minimize) {
			searcher.restrictDepth();
			if(!isQuiet){
				out.println("Restricting search depth to " + (length - 1));
			}
			out.flush();
		} else if (numErrors >= errorBound) {
			searchTruncated = true;
			throw new ExcessiveErrorException(errorBound);
		}
	}

	/**
	 * @throws ExcessiveErrorException
	 *             if the number of errors reported has exceeded the specified
	 *             bound
	 */
	public void report(LogEntry entry) throws FileNotFoundException {
		if (searcher == null) {
			if(!entry.getConfiguration().isQuiet()){
				out.println("Error " + numErrors + ":");
				entry.printBody(out);
			}
			numErrors++;
		} else
			reportWithSearcher(entry);
	}

	/**
	 * Returns the minimal size of a counterexample reported to this logger, or
	 * -1 if no counterexamples have been logged. The size is the length of the
	 * depth first search stack at the time of the log event.
	 * 
	 * @return the minimal counterexample size
	 */
	public int getMinimalCounterexampleSize() {
		return minimalCounterexampleSize;
	}

}
