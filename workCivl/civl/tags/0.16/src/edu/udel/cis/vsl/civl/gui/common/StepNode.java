package edu.udel.cis.vsl.civl.gui.common;

import edu.udel.cis.vsl.civl.kripke.IF.AtomicStep;

/**
 * Node corresponding to a Step
 */
public class StepNode extends GUINODE {
	static final long serialVersionUID = 1L;
	private AtomicStep step;

	public StepNode(String name, AtomicStep s) {
		super(name);
		step = s;
	}

	public AtomicStep getStep() {
		return step;
	}

	public GUINodeKind getKind() {
		return GUINodeKind.STEP_NODE;
	}

}
