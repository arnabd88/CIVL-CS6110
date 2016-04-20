package edu.udel.cis.vsl.civl.transition;

import java.util.ArrayList;

/**
 * This represents a complete transition of CIVL, which contains a number of
 * steps performing by a particular process.
 * 
 * The following is an example of a complete transition:<br>
 * <code>
 * Transition 11: State 10, proc 0: <br>
 *   12-&gt;14: LOOP_TRUE_BRANCH at f0:29.18-23 "i < n";<br>
 *   14-&gt;16: $spawn dine(i) at f0:29.30-44 "$spawn dine(i)";<br>
 *   16-&gt;12: i = (i+1) at f0:29.25-28 "i++";<br>
 *   --&gt; State 11
 * </code>
 * 
 * @author Manchun Zheng
 * 
 */
public class CompoundTransition extends Transition {
	private int pid;
	private int processIdentifier;
	private ArrayList<Step> steps;

	public CompoundTransition(int pid, int processIdentifier) {
		this.pid = pid;
		this.processIdentifier = processIdentifier;
		this.steps = new ArrayList<>();
	}

	public void addStep(Step step) {
		this.steps.add(step);
	}

	public Step getStep(int index) {
		return this.steps.get(index);
	}

	public int getNumOfSteps() {
		return this.steps.size();
	}

	public Iterable<Step> getSteps() {
		return this.steps;
	}

	public int pid() {
		return pid;
	}

	public void setPid(int pid) {
		this.pid = pid;
	}

	public int processIdentifier() {
		return processIdentifier;
	}

	public void setProcessIdentifier(int processIdentifier) {
		this.processIdentifier = processIdentifier;
	}

	@Override
	public String toString() {
		StringBuffer result = new StringBuffer();
		int count = 0;

		result.append("Proc ");
		result.append(this.processIdentifier);
		result.append(" (process<");
		result.append(this.pid);
		result.append(">):\n");
		for (Step step : this.steps) {
			result.append("| ");
			result.append("Step ");
			result.append(count);
			result.append(": ");
			result.append(step.toString());
			result.append("\n");
			count++;
		}
		return result.toString();
	}
}
