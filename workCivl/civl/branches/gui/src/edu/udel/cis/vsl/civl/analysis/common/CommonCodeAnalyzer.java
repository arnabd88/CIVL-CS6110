package edu.udel.cis.vsl.civl.analysis.common;

import edu.udel.cis.vsl.civl.analysis.IF.CodeAnalyzer;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * A general and abstract implementation of a code analyzer.
 * 
 * @author Manchun Zheng
 *
 */
public abstract class CommonCodeAnalyzer implements CodeAnalyzer {

	@Override
	public void analyze(State state, int pid, CallOrSpawnStatement statement,
			SymbolicExpression[] argumentValues) {
		return;
	}

}
