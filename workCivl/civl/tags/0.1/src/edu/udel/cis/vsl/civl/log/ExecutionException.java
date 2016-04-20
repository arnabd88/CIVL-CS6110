package edu.udel.cis.vsl.civl.log;

import edu.udel.cis.vsl.civl.util.ExecutionProblem;

public class ExecutionException extends ExecutionProblem {

	/**
	 * 
	 */
	private static final long serialVersionUID = -2334677214536658953L;

	public ExecutionException(ErrorKind kind, Certainty certainty,
			String message) {
		super(kind, certainty, message);
		// TODO Auto-generated constructor stub
	}

}
