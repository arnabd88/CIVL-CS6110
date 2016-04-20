/**
 * 
 */
package edu.udel.cis.vsl.civl.log.IF;

import java.io.PrintStream;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.gmc.GMCConfiguration;
import edu.udel.cis.vsl.gmc.LogEntry;

/**
 * This represents an entry in the error log of CIVL.
 * 
 * @author zirkel
 * 
 */
public class CIVLLogEntry extends LogEntry {

	private CIVLExecutionException problem;

	public CIVLLogEntry(GMCConfiguration configuration,
			CIVLExecutionException problem) {
		super(configuration);
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

			if (result != 0)
				return result;
			result = problem.kind().compareTo(thatProblem.kind());
			if (result != 0)
				return result;
			else {
				CIVLSource source1 = problem.getSource(), source2 = thatProblem
						.getSource();

				if (source1 != null && source2 != null) {
					if (source1.equals(source2))
						return 0;
					else
						return source1.toString().compareTo(source2.toString());
				} else if (source1 == null && source2 != null)
					return -1;
				else if (source1 != null & source2 == null)
					return 1;
				else
					return 0;
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
				CIVLSource source1 = problem.getSource(), source2 = thatProblem
						.getSource();

				if (source1 != null && source2 != null) {
					if (source1.equals(source2))
						return true;
					else
						return source1.toString().equals(source2.toString());
				} else if (source1 == null && source2 != null)
					return false;
				else if (source1 != null & source2 == null)
					return false;
				else
					return true;
			}
		}
		return false;
	}

}
