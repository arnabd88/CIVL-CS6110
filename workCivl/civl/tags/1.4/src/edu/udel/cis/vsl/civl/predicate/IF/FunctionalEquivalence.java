package edu.udel.cis.vsl.civl.predicate.IF;

import java.util.Map;
import java.util.Set;

import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * A functional equivalence predicate contains a specification output, which is
 * a set of pairs (pathcondition, output variable map), and is checked at the
 * final state of the program. Given a specification and an implementation, the
 * predicate is true if for every final state (p, o) of the implementation,
 * there exists at least one entry (p', o') in the specification output such
 * that p && p' -&gt; o=o'. Formally, suppose the specification output is {(p0,
 * o0), (p1, o1), ...}, then the following predicate must be valid: p -&gt; (p1
 * && o=o1 || p2 && o=o2 || ...).
 * 
 * @author Manchun Zheng
 *
 */
public interface FunctionalEquivalence extends CIVLStatePredicate {

	/**
	 * The specification output of this predicate, which is a list of tuples of
	 * path condition and a map of (output) variables and their values.
	 * 
	 * @return
	 */
	Map<BooleanExpression, Set<Pair<State, SymbolicExpression[]>>> specificationOutputs();

	// /**
	// * Add a new entry to the specification output using the given path
	// * condition and the outputs.
	// *
	// * @param pathcondition
	// * @param outputs
	// */
	// void addSpecificationOutputEntry(BooleanExpression pathcondition,
	// List<SymbolicExpression> outputs);

	// /**
	// * Set the list of output variables.
	// */
	// void setOutputVariables(List<Variable> outputs);
}
