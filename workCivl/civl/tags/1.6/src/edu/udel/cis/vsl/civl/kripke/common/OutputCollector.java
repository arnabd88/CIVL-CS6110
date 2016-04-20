package edu.udel.cis.vsl.civl.kripke.common;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * This class collects the values of output variables of the final state.
 * 
 * @author Manchun Zheng
 *
 */
public class OutputCollector {

	Map<BooleanExpression, Set<Pair<State, SymbolicExpression[]>>> collectedOutputs = new HashMap<>();
	String[] outptutNames;
	private Set<State> checkedState = new HashSet<>();
	private int[] outputIds;
	private int numOutputs;

	public OutputCollector(Model model) {
		List<Variable> outputVariables = model.outputVariables();
		int i = 0;
		numOutputs = outputVariables.size();

		outptutNames = new String[this.numOutputs];
		outputIds = new int[this.numOutputs];
		for (Variable variable : outputVariables) {
			outputIds[i] = variable.vid();
			outptutNames[i] = variable.name().name();
			i++;
		}
	}

	void collectOutputs(State state) {
		if (!state.isFinalState())
			return;
		if (this.checkedState.contains(state))
			return;

		// state.print(System.out);
		BooleanExpression pc = state.getPathCondition();
		int rootScope = 0;
		Set<Pair<State, SymbolicExpression[]>> outputSet = this.collectedOutputs
				.get(pc);
		SymbolicExpression[] outputs = new SymbolicExpression[this.numOutputs];

		this.checkedState.add(state);
		for (int i = 0; i < this.numOutputs; i++) {
			outputs[i] = state.getVariableValue(rootScope, this.outputIds[i]);
		}
		if (outputSet != null) {
			outputSet.add(new Pair<>(state, outputs));
		} else {
			outputSet = new LinkedHashSet<>();
			outputSet.add(new Pair<>(state, outputs));
			this.collectedOutputs.put(pc, outputSet);
		}
	}
}
