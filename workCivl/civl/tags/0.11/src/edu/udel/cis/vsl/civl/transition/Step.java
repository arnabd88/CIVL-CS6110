package edu.udel.cis.vsl.civl.transition;

import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.state.IF.State;

/**
 * This represents a statement executed from a state to a new state.
 * 
 * @author Manchun Zheng
 * 
 */
public class Step {
	private State start;
	private State target;
	private Statement statement;

	public Step(State start, State target, Statement statement) {
		this.start = start;
		this.target = target;
		this.statement = statement;
	}

	public State start() {
		return start;
	}

	public void setStart(State start) {
		this.start = start;
	}

	public State target() {
		return target;
	}

	public void setTarget(State target) {
		this.target = target;
	}

	public Statement statement() {
		return statement;
	}

	public void setStatement(Statement statement) {
		this.statement = statement;
	}

	@Override
	public String toString() {
		StringBuffer result = new StringBuffer();

		result.append(this.start.toString());
		result.append(" - ");
		result.append(statement.toString());
		result.append(" -> ");
		result.append(this.target.toString());
		return result.toString();
	}
}
