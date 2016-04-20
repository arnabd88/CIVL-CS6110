package edu.udel.cis.vsl.civl.run.common;

public class VerificationStatus {
	public int maxProcessCount;
	public int numStates;
	public int numSavedStates;
	public int numMatchedStates;
	public long numTransitions;
	public int numTraceSteps;

	public VerificationStatus(int maxProcCount, int states, int savedStates,
			int matchedStates, long trans, int traceSteps) {
		this.maxProcessCount = maxProcCount;
		this.numStates = states;
		this.numSavedStates = savedStates;
		this.numMatchedStates = matchedStates;
		this.numTransitions = trans;
		this.numTraceSteps = traceSteps;
	}
}