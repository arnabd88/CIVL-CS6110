/**
 * 
 */
package edu.udel.cis.vsl.civl.log;

import java.io.PrintWriter;

import edu.udel.cis.vsl.civl.err.CIVLExecutionException;

/**
 * @author zirkel
 * 
 */
public class LogEntry {

	/** The id number of this log entry, unique within the log. */
	private int id;

	/**
	 * A measure of the size of the counterexample.
	 */
	private int size;

	private CIVLExecutionException problem;

	/** The log to which this entry belongs. */
	private ErrorLog log;

	private int hashCode;

	/**
	 * 
	 */
	public LogEntry(ErrorLog log, CIVLExecutionException problem, int size) {
		this.log = log;
		this.problem = problem;
		this.size = size;
		this.hashCode = problem.hashCode();
	}

	public int hashCode() {
		return hashCode;
	}

	public ErrorLog log() {
		return log;
	}

	public int size() {
		return size;
	}

	public int id() {
		return id;
	}

	public CIVLExecutionException problem() {
		return problem;
	}

	public void setId(int id) {
		this.id = id;
	}

	public void print(PrintWriter out) {
		out.print("Error " + id + ": ");
		out.print(problem);
		out.println();
	}

}
