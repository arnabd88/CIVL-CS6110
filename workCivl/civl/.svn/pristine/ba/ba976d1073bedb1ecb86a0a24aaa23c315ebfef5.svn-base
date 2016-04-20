package edu.udel.cis.vsl.civl.predicate.IF;

import java.util.Map;
import java.util.Set;

import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.kripke.IF.Enabler;
import edu.udel.cis.vsl.civl.kripke.IF.LibraryEnablerLoader;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.predicate.common.CommonAndPredicate;
import edu.udel.cis.vsl.civl.predicate.common.CommonDeadlock;
import edu.udel.cis.vsl.civl.predicate.common.CommonFunctionalEquivalence;
import edu.udel.cis.vsl.civl.predicate.common.CommonPotentialDeadlock;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

public class Predicates {

	public static Deadlock newDeadlock(SymbolicUniverse universe,
			Enabler enabler, SymbolicAnalyzer symbolicAnalyzer) {
		return new CommonDeadlock(universe, enabler, symbolicAnalyzer);
	}

	public static PotentialDeadlock newPotentialDeadlock(
			SymbolicUniverse universe, Enabler enabler,
			LibraryEnablerLoader loader, Evaluator evaluator,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer) {
		return new CommonPotentialDeadlock(universe, enabler, loader,
				evaluator, modelFactory, symbolicUtil, symbolicAnalyzer);
	}

	public static FunctionalEquivalence newFunctionalEquivalence(
			SymbolicUniverse universe,
			SymbolicAnalyzer symbolicAnalyzer,
			String[] outputNames,
			Map<BooleanExpression, Set<Pair<State, SymbolicExpression[]>>> specOutputs) {
		return new CommonFunctionalEquivalence(universe, symbolicAnalyzer,
				outputNames, specOutputs);
	}

	public static AndPredicate newAndPredicate(CIVLStatePredicate predicate) {
		return new CommonAndPredicate(predicate);
	}
}
