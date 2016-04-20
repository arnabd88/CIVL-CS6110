package edu.udel.cis.vsl.civl.gui.common;

import edu.udel.cis.vsl.civl.state.IF.State;

/**
 * Node corresponding to a State
 */
public class StateNode extends GUINODE {
	static final long serialVersionUID = 1L;
	private State state;

	public StateNode(String name, State s) {
		super(name);
		state = s;
	}

	public State getState() {
		return state;
	}

	public GUINodeKind getKind() {
		return GUINodeKind.STATE_NODE;
	}

}