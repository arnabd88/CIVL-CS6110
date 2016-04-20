package edu.udel.cis.vsl.civl.analysis.IF;

import java.io.PrintStream;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.civl.analysis.common.AbsCallAnalyzer;
import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

public class Analysis {

	public static final String ABS = "abs";

	public static void staticAnalysis(Statement statement,
			List<CodeAnalyzer> analyzers) {
		for (CodeAnalyzer analyzer : analyzers)
			analyzer.staticAnalysis(statement);
	}

	public static List<CodeAnalyzer> getAnalyzers(CIVLConfiguration config,
			SymbolicUniverse universe) {
		List<CodeAnalyzer> result = new LinkedList<>();

		if (config.analyzeAbs())
			result.add(new AbsCallAnalyzer(universe));
		return result;
	}

	public static void analyzeCall(List<CodeAnalyzer> analyzers, State state,
			int pid, CallOrSpawnStatement statement,
			SymbolicExpression[] arguments) {
		for (CodeAnalyzer analyzer : analyzers)
			analyzer.analyze(state, pid, statement, arguments);
	}

	public static void printResults(List<CodeAnalyzer> analyzers,
			PrintStream out) {
		for (CodeAnalyzer analyzer : analyzers)
			analyzer.printAnalysis(out);
	}
}
