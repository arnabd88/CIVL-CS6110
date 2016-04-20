package edu.udel.cis.vsl.civl.predicate.common;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import edu.udel.cis.vsl.civl.log.IF.CIVLExecutionException;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.Certainty;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.predicate.IF.FunctionalEquivalence;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

public class CommonFunctionalEquivalence extends CommonCIVLStatePredicate
		implements FunctionalEquivalence {

	private boolean debug = false;
	private String[] outputNames;
	private Map<BooleanExpression, Set<SymbolicExpression[]>> specificationOutputs = new LinkedHashMap<>();
	private int numOutputs;

	public CommonFunctionalEquivalence(SymbolicUniverse universe,
			SymbolicAnalyzer symbolicAnalyzer, String[] outputNames,
			Map<BooleanExpression, Set<SymbolicExpression[]>> specOutputs) {
		this.outputNames = outputNames;
		this.specificationOutputs = specOutputs;
		this.numOutputs = this.outputNames.length;
		this.universe = universe;
		this.symbolicAnalyzer = symbolicAnalyzer;
		if (debug)
			System.out.println("Specification: \n" + this.toString());
		System.out.print(this.toString());
	}

	@Override
	public boolean holdsAt(State state) {
		if (!state.isFinalState() || outputNames.length < 1)
			return false;

		SymbolicExpression[] implOutputs = state
				.getOutputValues(this.outputNames);
		BooleanExpression predicate;
		// p -> (p1 && (o=o11 || o = o12 || ..) || p2 && (o=o21 || o=o22 || ...
		// ) || ...).
		BooleanExpression pc = state.getPathCondition();
		BooleanExpression disjunction = null;
		Reasoner reasoner = universe.reasoner(universe.trueExpression());
		boolean result;

		for (Map.Entry<BooleanExpression, Set<SymbolicExpression[]>> specPcAndOuts : this.specificationOutputs
				.entrySet()) {
			BooleanExpression clause = specPcAndOuts.getKey();// pc_spec
			Set<SymbolicExpression[]> specOutsSet = specPcAndOuts.getValue();
			BooleanExpression containsEqual = null;

			for (SymbolicExpression[] specOuts : specOutsSet) {
				BooleanExpression outEqual = null;

				// outEqual = (o1 = o11 && o2= o22 && ...)
				for (int i = 0; i < numOutputs; i++) {
					SymbolicExpression specOut = specOuts[i];
					SymbolicExpression implOut = implOutputs[i];

					if (outEqual == null)
						outEqual = universe.equals(specOut, implOut);
					else
						outEqual = universe.and(outEqual,
								universe.equals(specOut, implOut));
				}
				if (containsEqual == null)
					containsEqual = outEqual;
				else
					// containsEqual = (outEqual1 || outEqual2 || ...)
					containsEqual = universe.or(containsEqual, outEqual);
			}
			clause = universe.and(clause, containsEqual);
			if (disjunction == null)
				disjunction = clause;
			else
				disjunction = universe.or(disjunction, clause);
		}
		predicate = universe.implies(pc, disjunction);
		predicate = (BooleanExpression) universe.canonic(predicate);
		if (debug) {
			System.out.print(this.symbolicAnalyzer.stateToString(state));
			System.out.print("predicate: ");
			System.out.println(predicate);
		}
		result = !reasoner.isValid(predicate);
		if (result) {
			StringBuffer msg = new StringBuffer();

			msg.append(this.toString());
			msg.append("\nsaw implementation output:\n");
			msg.append("pc: ");
			msg.append(pc);
			msg.append(", output: ");
			for (int i = 0; i < this.numOutputs; i++) {
				if (i > 0)
					msg.append(", ");
				msg.append(this.symbolicAnalyzer.symbolicExpressionToString(
						null, state,null, implOutputs[i]));
			}
			violation = new CIVLExecutionException(
					ErrorKind.FUNCTIONAL_EQUIVALENCE, Certainty.PROVEABLE,
					null, msg.toString(),
					symbolicAnalyzer.stateInformation(state), null);
		}
		return result;
	}

	@Override
	public String explanation() {
		if (violation == null)
			return "Functional Equivalence met";
		return violation.getMessage();
	}

	@Override
	public Map<BooleanExpression, Set<SymbolicExpression[]>> specificationOutputs() {
		return this.specificationOutputs;
	}

	@Override
	public String toString() {
		StringBuffer result = new StringBuffer();
		// int k=0;

		result.append("Output variables:\n");
		for (int i = 0; i < this.numOutputs; i++) {
			result.append(this.outputNames[i]);
			result.append("\n");
		}
		result.append("Specification output values:");
		for (Map.Entry<BooleanExpression, Set<SymbolicExpression[]>> entry : this.specificationOutputs
				.entrySet()) {
			int j = 0;

			result.append("\npc: ");
			result.append(entry.getKey());
			result.append(", output: {");
			for (SymbolicExpression[] outputs : entry.getValue()) {
				if (j > 0)
					result.append(", ");
				result.append("(");
				for (int k = 0; k < this.numOutputs; k++) {
					if (k > 0)
						result.append(", ");
					result.append(this.symbolicAnalyzer
							.symbolicExpressionToString(null, null, null,outputs[k]));
				}
				result.append(")");
				j++;
			}
			result.append("}");
		}
		return result.toString();
	}
}
