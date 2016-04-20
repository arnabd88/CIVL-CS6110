package edu.udel.cis.vsl.civl.analysis.common;

import java.io.PrintStream;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import edu.udel.cis.vsl.civl.analysis.IF.Analysis;
import edu.udel.cis.vsl.civl.analysis.IF.CodeAnalyzer;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * This analyzer is dedicated for analyzing abs(arg) calls (of math library).
 * The purpose is keep track of the value of the argument arg:
 * 
 * <ul>
 * <li>NONE: function is never called (this is the initial state)</li>
 * <li>+: function is called at least once, and all calls satisfy the argument
 * must be &gt;= 0 (i.e., you could prove that always arg &gt;=0) and at least
 * one call may have an argument that is &gt;0 (i.e., you could not prove that
 * arg =0)</li>
 * <li>0: function is called at least once, and all calls satisfy the argument
 * must be 0 (you could prove that every time arg = 0)</li>
 * <li>-: function is called at least once, and all calls satisfy arg &lt;=0 and
 * at least once call satisfy arg &lt;0 (dual to +)</li>
 * <li>: function is called at least once, at least one call has argument which
 * could be &lt;0 (i.e., you could not prove arg&gt;=0), at least one call has
 * argument which could be &gt;0 (i.e., you could not prove arg&lt;=0)</li>
 * </ul>
 * 
 * +: Y (pc && arg &gt; 0) +: N (pc -&gt; arg &lt;=0) +: ? (none of the above)
 * -: Y -: N -: ? 0: Y 0: N 0: ?
 * 
 * @author zmanchun
 *
 */
public class AbsCallAnalyzer extends CommonCodeAnalyzer implements CodeAnalyzer {
	public enum AbsType {
		NONE, YES, // can be
		NO, // never
		MAYBE;// I don't know
		@Override
		public String toString() {
			switch (this) {
			case YES:
				return "Y";
			case NO:
				return "N";
			case MAYBE:
				return "?";
			case NONE:
				return "NA";
			default:
				return "";
			}
		}
	}

	class AbsStatus {
		AbsType positive = AbsType.NONE;
		AbsType negative = AbsType.NONE;
		AbsType zero = AbsType.NONE;

		@Override
		public String toString() {
			return "-:" + negative + " " + "0:" + zero + " " + "+:" + positive;
		}
	}

	private Set<CallOrSpawnStatement> unpreprocessedStatements = new HashSet<>();
	private Map<CallOrSpawnStatement, AbsStatus> result = new LinkedHashMap<>();
	private SymbolicUniverse universe;
	private NumericExpression zero;
	private Reasoner reasoner;

	public AbsCallAnalyzer(SymbolicUniverse universe) {
		this.universe = universe;
		this.zero = universe.zeroInt();
		this.reasoner = universe.reasoner(universe.trueExpression());
	}

	@Override
	public void staticAnalysis(Statement statement) {

		if (statement instanceof CallOrSpawnStatement) {
			CallOrSpawnStatement call = (CallOrSpawnStatement) statement;
			CIVLFunction function = call.function();

			if (function == null)
				this.unpreprocessedStatements.add(call);
			else if (function.name().name().equals(Analysis.ABS)
					&& function.getSource().getFileName().equals("stdlib.cvl")) {
				result.put(call, new AbsStatus());
			}
		}
	}

	private ResultType isSatisfiable(BooleanExpression predicate) {
		BooleanExpression claim = universe.not(predicate);
		ResultType result = reasoner.valid(claim).getResultType();

		if (result == ResultType.YES)
			return ResultType.NO;
		else if (result == ResultType.NO)
			return ResultType.YES;
		return ResultType.MAYBE;
	}

	private BooleanExpression canNegative(BooleanExpression pathCondition,
			NumericExpression value) {
		BooleanExpression negative = universe.lessThan(value, zero);

		return universe.and(pathCondition, negative);
	}

	private BooleanExpression canPositive(BooleanExpression pathCondition,
			NumericExpression value) {
		BooleanExpression positive = universe.lessThan(zero, value);

		return universe.and(pathCondition, positive);
	}

	private BooleanExpression canZero(BooleanExpression pathCondition,
			NumericExpression value) {
		BooleanExpression isZero = universe.equals(zero, value);

		return universe.and(pathCondition, isZero);
	}

	/**
	 * (pc -> arg != 0) is valid: equivalent to (pc -> arg != 0) with certainty
	 * YES.
	 * */
	private ResultType neverZero(BooleanExpression pathCondition,
			NumericExpression value) {
		BooleanExpression notZero = universe.neq(value, zero);
		BooleanExpression claim = universe.implies(pathCondition, notZero);

		return reasoner.valid(claim).getResultType();
	}

	private ResultType neverPositive(BooleanExpression pathCondition,
			NumericExpression value) {
		BooleanExpression notPositive = universe.lessThanEquals(value, zero);
		BooleanExpression claim = universe.implies(pathCondition, notPositive);

		return reasoner.valid(claim).getResultType();
	}

	private ResultType neverNegative(BooleanExpression pathCondition,
			NumericExpression value) {
		BooleanExpression notNegative = universe.lessThanEquals(zero, value);
		BooleanExpression claim = universe.implies(pathCondition, notNegative);

		return reasoner.valid(claim).getResultType();
	}

	private void analyzeZero(AbsStatus status, BooleanExpression pathCondition,
			NumericExpression argValue) {
		ResultType newResult;

		switch (status.zero) {
		case YES:// no need to check any more
			break;
		case NO: {
			newResult = this.neverZero(pathCondition, argValue);
			switch (newResult) {
			case YES:
				break;
			case NO:
				if (this.isSatisfiable(canZero(pathCondition, argValue)) == ResultType.YES) {
					status.zero = AbsType.YES;
					break;
				}
			case MAYBE:
				status.zero = AbsType.MAYBE;
				break;
			default:
			}
			break;
		}
		case MAYBE: {
			newResult = this.isSatisfiable(canZero(pathCondition, argValue));

			if (newResult == ResultType.YES)
				status.zero = AbsType.YES;
			break;
		}
		case NONE: {
			newResult = this.isSatisfiable(canZero(pathCondition, argValue));

			if (newResult == ResultType.YES)
				status.zero = AbsType.YES;
			else {
				newResult = this.neverZero(pathCondition, argValue);

				if (newResult == ResultType.YES)
					status.zero = AbsType.NO;
				else
					status.zero = AbsType.MAYBE;
			}
			break;
		}
		default:
		}
	}

	private void analyzePositive(AbsStatus status,
			BooleanExpression pathCondition, NumericExpression argValue) {
		ResultType newResult;

		switch (status.positive) {
		case YES:// no need to check any more
			break;
		case NO: {
			newResult = this.neverPositive(pathCondition, argValue);
			switch (newResult) {
			case YES:
				break;
			case NO:
				if (this.isSatisfiable(canPositive(pathCondition, argValue)) == ResultType.YES) {
					status.positive = AbsType.YES;
					break;
				}
			case MAYBE:
				status.positive = AbsType.MAYBE;
				break;
			default:
			}
			break;
		}
		case MAYBE: {
			newResult = this
					.isSatisfiable(canPositive(pathCondition, argValue));

			if (newResult == ResultType.YES)
				status.positive = AbsType.YES;
			break;
		}
		case NONE: {
			newResult = this
					.isSatisfiable(canPositive(pathCondition, argValue));

			if (newResult == ResultType.YES)
				status.positive = AbsType.YES;
			else {
				newResult = this.neverPositive(pathCondition, argValue);

				if (newResult == ResultType.YES)
					status.positive = AbsType.NO;
				else
					status.positive = AbsType.MAYBE;
			}
			break;
		}
		default:
		}
	}

	private void analyzeNegative(AbsStatus status,
			BooleanExpression pathCondition, NumericExpression argValue) {
		ResultType newResult;

		switch (status.negative) {
		case YES:// no need to check any more
			break;
		case NO: {
			newResult = this.neverNegative(pathCondition, argValue);
			switch (newResult) {
			case YES:
				break;
			case NO:
				if (this.isSatisfiable(canNegative(pathCondition, argValue)) == ResultType.YES) {
					status.negative = AbsType.YES;
					break;
				}
			case MAYBE:
				status.negative = AbsType.MAYBE;
				break;
			default:
			}
			break;
		}
		case MAYBE: {
			newResult = this
					.isSatisfiable(canNegative(pathCondition, argValue));

			if (newResult == ResultType.YES)
				status.negative = AbsType.YES;
			break;
		}
		case NONE: {
			newResult = this
					.isSatisfiable(canNegative(pathCondition, argValue));

			if (newResult == ResultType.YES)
				status.negative = AbsType.YES;
			else {
				newResult = this.neverNegative(pathCondition, argValue);

				if (newResult == ResultType.YES)
					status.negative = AbsType.NO;
				else
					status.negative = AbsType.MAYBE;
			}
			break;
		}
		default:
		}
	}

	@Override
	public void analyze(State state, int pid, CallOrSpawnStatement statement,
			SymbolicExpression[] argumentValues) {
		AbsStatus status = this.result.get(statement);
		BooleanExpression pathCondition = state.getPathCondition();
		NumericExpression argValue = (NumericExpression) argumentValues[0];

		this.analyzeZero(status, pathCondition, argValue);
		this.analyzePositive(status, pathCondition, argValue);
		this.analyzeNegative(status, pathCondition, argValue);
		return;
	}

	@Override
	public void printAnalysis(PrintStream out) {
		out.println("\n=== abs call analysis ===");
		if (result.size() > 0) {
			for (Map.Entry<CallOrSpawnStatement, AbsStatus> entry : result
					.entrySet()) {
				CallOrSpawnStatement key = entry.getKey();
				AbsStatus value = entry.getValue();

				out.println(value + " " + key.getSource().getContent());
			}
			out.println();
			out.println("+: argument > 0");
			out.println("-: argument < 0");
			out.println("0: argument = 0");
			out.println("Y: at least one");
			out.println("N: never");
			out.println("?: unknown");
			// out.println("*: argument could be anything");
		} else
			out.println("The program doesn't have any reachable abs function call.");
	}

}
