/**
 * 
 */
package edu.udel.cis.vsl.civl.log;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.util.LinkedHashMap;
import java.util.Map;

import edu.udel.cis.vsl.civl.state.State;
import edu.udel.cis.vsl.civl.transition.Transition;
import edu.udel.cis.vsl.civl.transition.TransitionSequence;
import edu.udel.cis.vsl.gmc.DfsSearcher;

/**
 * @author zirkel
 * 
 */
public class ErrorLog {

	private String line = "--------------------------------------------------------------------------------";
	private PrintWriter out;
	private int numReports = 0;
	private int errorBound = 1;
	private int numEntries = 0;
	private Map<LogEntry, LogEntry> entryMap = new LinkedHashMap<LogEntry, LogEntry>();
	private DfsSearcher<State, Transition, TransitionSequence> searcher;
//	private File workingDirectory;

	/**
	 * 
	 */
	public ErrorLog(PrintWriter out, File workingDirectory) {
		this.searcher = null;
		this.out = out;
//		this.workingDirectory = workingDirectory;
	}

	/**
	 * Report an error associated to the execution of a specified element in a
	 * model
	 * 
	 * @throws FileNotFoundException
	 */
	public void report(ExecutionException error) {
		int size = (searcher == null ? 0 : searcher.stack().size());
		processLogEntry(new LogEntry(this, error, size));
		considerQuitting();
	}

	private void considerQuitting() {
		int numErrors = entryMap.size();

		if (numErrors >= errorBound) {
			throw new ExcessiveErrorException(numErrors);
		}
	}

	public String name() {
		if (searcher == null)
			return null;
		else
			return searcher.name();
	}

	private void processLogEntry(LogEntry entry) {
		LogEntry oldEntry = entryMap.get(entry);

		numReports++;
		out.println("\n ********** Error Detected **********\n"
				+ entry.problem());
		out.flush();
		if (oldEntry != null) {
			if (entry.size() >= oldEntry.size()) {
				out.println("Previously found error is shorter: ignore thing one.\n");
				return;
			}
			entry.setId(oldEntry.id());
		}
		if (entry.id() < 0) {
			entry.setId(numEntries);
			numEntries++;
			entryMap.put(entry, entry);
		}
		if (searcher == null) {
			out.println("Encountered in initial state.\n");
			return;
		}
//		try {
//			String traceFilename = name() + "_" + entry.id() + ".trace";
//			File traceFile;
//			PrintWriter traceOut;
//
//			traceFile = new File(workingDirectory, traceFilename);
//			traceOut = new PrintWriter(traceFile);
//			out.print("Writing trace to " + traceFilename + "...");
//			out.flush();
//			writeTrace(traceOut);
//			out.println("done.\n");
//			out.flush();
//			traceOut.close();
//		} catch (FileNotFoundException e) {
//			out.println("Unable to open file for writing...exiting...");
//			print(out);
//			throw new RuntimeException(
//					"CIVL: Exiting due to inability to open log file.");
//		}
	}

	//TODO: take care of trace writing
//	private void writeTrace(PrintWriter traceOut) {
//		Stack<TransitionSequence> stack = searcher.stack();
//		int stackSize = stack.size();
//		traceOut.println();
//		for (int i = 0; i < stackSize; i++) {
//			TransitionSequence sequence = stack.elementAt(i);
//			
//			if (sequence.size() > 1) {
//				
//			}
//		}
//		// int stackSize = searcher.stack().size();
//		// TODO: Handle this printing.
//		// for (int i = 0; i < stackSize; i++) {
//		// TransitionSequence sequence = searcher.stack().elementAt(i);
//		//
//		// traceOut.println(sequence.)
//		// }
//
//	}

	public void setSearcher(
			DfsSearcher<State, Transition, TransitionSequence> searcher) {
		this.searcher = searcher;
	}

	public int errorBound() {
		return errorBound;
	}
	
	public void setErrorBound(int bound) {
		this.errorBound = bound;
	}

	public int numReports() {
		return numReports;
	}

	public void print(PrintWriter out) {
		out.println("================================ CIVL Error Log ================================");
		out.println();
		out.println("Number of errors reported........... " + numReports());
		out.println("Number of distinct errors........... " + entryMap.size());
		out.println();
		out.println(line);
		for (LogEntry entry : entryMap.values()) {
			out.println();
			entry.print(out);
			out.println();
			out.println(line);
		}
		out.flush();
	}

}
