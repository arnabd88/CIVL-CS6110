package edu.udel.cis.vsl.civl.predicate.common;

import edu.udel.cis.vsl.civl.predicate.IF.TrivialPredicate;
import edu.udel.cis.vsl.civl.state.IF.State;

public class CommonTrivialPredicate extends CommonCIVLStatePredicate implements
		TrivialPredicate {

	@Override
	public boolean holdsAt(State state) {
		return false;
	}

	@Override
	public String explanation() {
		return null;
	}

}
