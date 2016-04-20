package edu.udel.cis.vsl.civl.gui.common;

import edu.udel.cis.vsl.civl.kripke.IF.TraceStep;

/**
 * Node corresponding to a transition.
 */
public class TransitionNode extends GUINODE {
	static final long serialVersionUID = 1L;
	private TraceStep transition;

	public TransitionNode(String name, TraceStep t) {
		super(name);
		transition = t;
	}

	public TraceStep transition() {
		return transition;
	}

	public GUINodeKind getKind() {
		return GUINodeKind.TRANSITION_NODE;
	}
}
