/**
 * 
 */
package edu.udel.cis.vsl.civl.log.IF;

import java.io.PrintStream;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.config.IF.CIVLConstants.ErrorStateEquivalence;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.gmc.GMCConfiguration;
import edu.udel.cis.vsl.gmc.LogEntry;

/**
 * This represents an entry in the error log of CIVL.   LogEntry's are stored in a
 * collection that is ordered by the compareTo method and where the equals method
 * determines redundancy in terms of error reports.
 * 
 * Currently these two methods consult the CIVLConfiguration to determine what equivalence
 * should be applied to error states.   States that do not share the same problem kind
 * are always inequivalent.   There are three alternative criteria that are applied:
 *     LOC : require error locations in each proc to be the same for equivalence
 *     CALLSTACK : require call stacks in each proc to be the same for equivalence
 *     FULL : require the full trace, as expressed by the path condition, to be the same for equivalence
 * 
 * Additional equivalences are easy to implement by accessing components of the state.
 * 
 * @author zirkel
 * @author dwyer
 * 
 */
public class CIVLLogEntry extends LogEntry {

	private CIVLExecutionException problem;
	private CIVLConfiguration civlConfig;

	public CIVLLogEntry(CIVLConfiguration civlConfig,
			GMCConfiguration gmcConfig,
			CIVLExecutionException problem) {
		super(gmcConfig);
		this.civlConfig = civlConfig;
		this.problem = problem;
		problem.setReported();
	}

	public CIVLExecutionException problem() {
		return problem;
	}

	@Override
	public void printBody(PrintStream out) {
		out.println(problem.toString());
	}

	@Override
	public int compareTo(LogEntry that) {
		if (that instanceof CIVLLogEntry) {
			CIVLExecutionException thatProblem = ((CIVLLogEntry) that).problem;
			int result = problem.certainty().compareTo(thatProblem.certainty());

			// The "kind" of error detected must match.
			if (result != 0)
				return result;
			result = problem.kind().compareTo(thatProblem.kind());
			if (result != 0) {
				return result;
			} else {
				CIVLSource source1 = problem.getSource();
				CIVLSource source2 = thatProblem.getSource();
				State errorState1 = problem.state();
				State errorState2 = thatProblem.state();

				if (source1 == null && source2 != null) {
					return -1;
				} else if (source1 != null & source2 == null) {
					return 1;
				} else {
					if (civlConfig.errorStateEquiv() == ErrorStateEquivalence.LOC) {
						if (source1.equals(source2))
							return 0;
						else
							return source1.toString().compareTo(source2.toString());
						
					} else if (civlConfig.errorStateEquiv() == ErrorStateEquivalence.CALLSTACK) {
						// compare based on the call stack
						String callString1 = errorState1.callStackToString().toString();
						String callString2 = errorState2.callStackToString().toString();
						
						return callString1.compareTo(callString2);
						
					} else if (civlConfig.errorStateEquiv() == ErrorStateEquivalence.FULL) {
						// compare based on the full state
						assert errorState1.getCanonicId() != -1 : "Expected error state to be canonic";
						assert errorState2.getCanonicId() != -1 : "Expected error state to be canonic";
						
						String stateString1 = errorState1.getPathCondition().toString();
						String stateString2 = errorState2.getPathCondition().toString();
						
						return stateString1.compareTo(stateString2);
					} else {
						assert false : "Invalid error state equivalence";
					}
				}
			}
		}
		return -1;
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof CIVLLogEntry) {
			CIVLExecutionException thatProblem = ((CIVLLogEntry) obj).problem;

			if (!problem.certainty().equals(thatProblem.certainty()))
				return false;
			if (!problem.kind().equals(thatProblem.kind()))
				return false;
			else {
				CIVLSource source1 = problem.getSource();
				CIVLSource source2 = thatProblem.getSource();
				State errorState1 = problem.state();
				State errorState2 = thatProblem.state();

				if (source1 == null && source2 != null) {
					return false;
				} else if (source1 != null & source2 == null) {
					return false;
				} else {
					if (civlConfig.errorStateEquiv() == ErrorStateEquivalence.LOC) {
						if (source1.equals(source2))
							return true;
						else
							return source1.toString().equals(source2.toString());
						
					} else if (civlConfig.errorStateEquiv() == ErrorStateEquivalence.CALLSTACK) {
						// compare based on the call stack
						String callString1 = errorState1.callStackToString().toString();
						String callString2 = errorState2.callStackToString().toString();
						
						return callString1.equals(callString2);
						
					} else if (civlConfig.errorStateEquiv() == ErrorStateEquivalence.FULL) {
						// compare based on the full state
						assert errorState1.getCanonicId() != -1 : "Expected error state to be canonic";
						assert errorState2.getCanonicId() != -1 : "Expected error state to be canonic";
						
						String stateString1 = errorState1.getPathCondition().toString();
						String stateString2 = errorState2.getPathCondition().toString();
						
						return stateString1.equals(stateString2);
					} else {
						assert false : "Invalid error state equivalence";
					}
				}
			}
		}
		return false;
	}

}
