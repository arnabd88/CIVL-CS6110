package edu.udel.cis.vsl.gmc;

import java.util.ArrayList;
import java.util.Random;

public class RandomTransitionChooser<STATE, TRANSITION, TRANSITIONSEQUENCE>
		implements TransitionChooser<STATE, TRANSITION> {

	private long seed;

	private EnablerIF<STATE, TRANSITION, TRANSITIONSEQUENCE> enabler;

	private Random generator;

	public RandomTransitionChooser(
			EnablerIF<STATE, TRANSITION, TRANSITIONSEQUENCE> enabler, long seed) {
		this.enabler = enabler;
		this.seed = seed;
		this.generator = new Random(seed);
	}

	public RandomTransitionChooser(
			EnablerIF<STATE, TRANSITION, TRANSITIONSEQUENCE> enabler) {
		this(enabler, System.currentTimeMillis());
	}

	@Override
	public TRANSITION chooseEnabledTransition(STATE state)
			throws MisguidedExecutionException {
		ArrayList<TRANSITION> transitions = new ArrayList<TRANSITION>();
		TRANSITIONSEQUENCE sequence = enabler.enabledTransitions(state);
		int n, i;

		while (enabler.hasNext(sequence))
			transitions.add(enabler.next(sequence));
		n = transitions.size();
		if (n == 0)
			return null;
		i = generator.nextInt(n);
		return transitions.get(i);
	}

	public long getSeed() {
		return seed;
	}

}
