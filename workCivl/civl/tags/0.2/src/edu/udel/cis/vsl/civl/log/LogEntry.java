/**
 * 
 */
package edu.udel.cis.vsl.civl.log;

import java.io.PrintWriter;

import edu.udel.cis.vsl.civl.util.CIVLException;

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

	private CIVLException problem;

	/** The log to which this entry belongs. */
	private ErrorLog log;

	private int hashCode;

	/**
	 * 
	 */
	public LogEntry(ErrorLog log, CIVLException problem, int size) {
		this.log = log;
		this.problem = problem;
		this.size = size;
		this.hashCode = computeHashCode();
	}

	public int hashCode() {
		return hashCode;
	}
	
	private int computeHashCode() {
		int result = problem.kind().hashCode();

		if (problem instanceof ExecutionException) {
			result = ((ExecutionException) problem).hashCode();
		} else {
			throw new RuntimeException(
					"CIVL internal error: unknown kind of execution problem: "
							+ problem);
		}
		return result;
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
	
	public CIVLException problem() {
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
