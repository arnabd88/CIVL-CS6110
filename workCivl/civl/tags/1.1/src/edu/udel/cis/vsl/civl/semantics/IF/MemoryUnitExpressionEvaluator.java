package edu.udel.cis.vsl.civl.semantics.IF;

import edu.udel.cis.vsl.civl.model.IF.expression.MemoryUnitExpression;
import edu.udel.cis.vsl.civl.state.IF.MemoryUnitSet;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;

public interface MemoryUnitExpressionEvaluator {
	MemoryUnitSet evaluates(State state, int pid, MemoryUnitExpression memUnit,
			MemoryUnitSet muSet) throws UnsatisfiablePathConditionException;
}
