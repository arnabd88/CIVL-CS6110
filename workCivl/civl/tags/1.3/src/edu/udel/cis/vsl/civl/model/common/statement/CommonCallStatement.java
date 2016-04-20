package edu.udel.cis.vsl.civl.model.common.statement;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression.ExpressionKind;
import edu.udel.cis.vsl.civl.model.IF.expression.FunctionIdentifierExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.model.common.StaticAnalysisConfiguration;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;

/**
 * A function call or spawn. Either of the form f(x) or else v=f(x), i.e., the
 * left-hand side expression is optional.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonCallStatement extends CommonStatement implements
		CallOrSpawnStatement {

	private static final BitSet EMPTY_BITSET = new BitSet();

	private boolean isCall;

	private LHSExpression lhs = null;

	private Expression functionExpression;

	private List<Expression> arguments;

	/**
	 * A function call. Either of the form f(x) or else v=f(x).
	 * 
	 * @param source
	 *            The source location for this call statement.
	 * @param isCall
	 *            is this a call statement (not spawn)?
	 * @param function
	 *            The function.
	 * @param arguments
	 *            The arguments to the function.
	 */
	public CommonCallStatement(CIVLSource civlSource, Scope hscope,
			Scope lscope, Location source, Expression guard, boolean isCall,
			LHSExpression lhs, Expression functionExpression,
			List<Expression> arguments) {
		super(civlSource, hscope, lscope, source, guard);
		this.isCall = isCall;
		this.lhs = lhs;
		this.functionExpression = functionExpression;
		this.arguments = arguments;
	}

	/**
	 * @return The left hand side expression if applicable. Else null.
	 */
	@Override
	public LHSExpression lhs() {
		return lhs;
	}

	/**
	 * @return The function being called.
	 */
	@Override
	public CIVLFunction function() {
		if (this.functionExpression.expressionKind() == ExpressionKind.FUNCTION_IDENTIFIER)
			return ((FunctionIdentifierExpression) functionExpression)
					.function();
		return null;
	}

	@Override
	public Expression functionExpression() {
		return this.functionExpression;
	}

	/**
	 * @return The arguments to the function.
	 */
	@Override
	public List<Expression> arguments() {
		return arguments;
	}

	/**
	 * @param lhs
	 *            The left hand side expression if applicable. Else null.
	 */
	@Override
	public void setLhs(LHSExpression lhs) {
		this.lhs = lhs;
	}

	/**
	 * @param arguments
	 *            The arguments to the function.
	 */
	@Override
	public void setArguments(List<Expression> arguments) {
		this.arguments = arguments;
	}

	@Override
	public String toString() {
		String result = this.functionExpression.toString();
		boolean first = true;

		result += "(";
		for (Expression arg : arguments) {
			if (first)
				first = false;
			else
				result += ", ";
			result += arg.toString();
		}
		result += ")";
		if (!isCall)
			result = "$spawn " + result;
		if (lhs != null) {
			result = lhs + " = " + result;
		}
		return result;
	}

	@Override
	public boolean isCall() {
		return isCall;
	}

	@Override
	public boolean isSpawn() {
		return !isCall;
	}

	@Override
	public void calculateDerefs() {
		this.hasDerefs = false;
		if (this.lhs != null) {
			lhs.calculateDerefs();
			this.hasDerefs = this.hasDerefs || lhs.hasDerefs();
		}
		// if (this.arguments != null) {
		// for (Expression arg : this.arguments) {
		// arg.calculateDerefs();
		// this.hasDerefs = this.hasDerefs || arg.hasDerefs();
		// // early return
		// if (this.hasDerefs)
		// return;
		// }
		// }
	}

	@Override
	public void purelyLocalAnalysisOfVariables(Scope funcScope) {
		super.purelyLocalAnalysisOfVariables(funcScope);
		if (this.lhs != null)
			this.lhs.purelyLocalAnalysisOfVariables(funcScope);
		for (Expression arg : this.arguments) {
			arg.purelyLocalAnalysisOfVariables(funcScope);
		}
	}

	@Override
	public void purelyLocalAnalysis() {
		// if (this.isSystemCall()) {
		// this.purelyLocal = false;
		// return;
		// }
		this.guard().purelyLocalAnalysis();
		if (this.lhs != null) {
			this.lhs.purelyLocalAnalysis();
			if (!this.lhs.isPurelyLocal()) {
				this.purelyLocal = false;
				return;
			}
		}
		for (Expression arg : this.arguments) {
			arg.purelyLocalAnalysis();
			if (!arg.isPurelyLocal()) {
				this.purelyLocal = false;
				return;
			}
		}
		this.purelyLocal = this.guard().isPurelyLocal();
	}

	@Override
	public void replaceWith(ConditionalExpression oldExpression,
			VariableExpression newExpression) {
		int number = arguments.size();

		super.replaceWith(oldExpression, newExpression);
		for (int i = 0; i < number; i++) {
			Expression arg = arguments.get(i);

			if (arg == oldExpression) {
				arguments.set(i, newExpression);
				return;
			}
			arg.replaceWith(oldExpression, newExpression);
		}
	}

	@Override
	public Statement replaceWith(ConditionalExpression oldExpression,
			Expression newExpression) {
		Expression newGuard = guardReplaceWith(oldExpression, newExpression);
		CommonCallStatement newStatement = null;

		if (newGuard != null) {
			newStatement = new CommonCallStatement(this.getSource(),
					this.statementScope, this.lowestScope, this.source(),
					newGuard, this.isCall, lhs, this.functionExpression,
					this.arguments);
		} else {
			boolean hasNewArg = false;
			ArrayList<Expression> newArgs = new ArrayList<Expression>();
			int number = this.arguments.size();

			for (int i = 0; i < number; i++) {
				if (hasNewArg)
					newArgs.add(arguments.get(i));
				else {
					Expression newArg = arguments.get(i);
					newArg = newArg.replaceWith(oldExpression, newExpression);

					if (newArg != null) {
						newArgs.add(newArg);
						hasNewArg = true;
					} else
						newArgs.add(arguments.get(i));
				}
			}
			if (hasNewArg) {
				newStatement = new CommonCallStatement(this.getSource(),
						this.statementScope, this.lowestScope, this.source(),
						this.guard(), this.isCall, lhs,
						this.functionExpression, newArgs);
			}
		}
		return newStatement;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		Set<Variable> result = new HashSet<>();

		if (lhs != null) {
			Variable lhsVariable = lhs.variableWritten(scope);

			if (lhsVariable != null)
				result.add(lhsVariable);
		}
		if (arguments != null) {
			Set<Variable> argumentResult;
			int n = this.arguments.size();
			CIVLFunction function = this.function();
			BitSet ignored = EMPTY_BITSET;

			if (function != null)
				ignored = StaticAnalysisConfiguration
						.getIgnoredArgumenets(function);
			for (int i = 0; i < n; i++) {
				if (ignored.get(i))
					continue;

				Expression argument = arguments.get(i);

				argumentResult = argument.variableAddressedOf(scope);
				if (argumentResult != null)
					result.addAll(argumentResult);
			}
		}
		return result;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		Set<Variable> result = new HashSet<>();

		if (arguments != null) {
			Set<Variable> argumentResult;
			int n = this.arguments.size();
			CIVLFunction function = this.function();
			BitSet ignored = EMPTY_BITSET;

			if (function != null)
				ignored = StaticAnalysisConfiguration
						.getIgnoredArgumenets(function);
			for (int i = 0; i < n; i++) {
				if (ignored.get(i))
					continue;

				Expression argument = arguments.get(i);

				argumentResult = argument.variableAddressedOf();
				if (argumentResult != null)
					result.addAll(argumentResult);
			}
		}
		return result;
	}

	@Override
	public StatementKind statementKind() {
		return StatementKind.CALL_OR_SPAWN;
	}

	@Override
	public boolean isSystemCall() {
		CIVLFunction function = this.function();

		if (this.isCall && function != null && function.isLibraryFunction()) {
			return true;
		}
		return false;
	}

	@Override
	public String locationStepString() {
		String result = (source() == null ? "??" : source().id()) + "->";
		CIVLFunction function = this.function();

		if (this.isCall && function != null && function.isNormal()) {
			result += Integer.toString(function.startLocation().id());
			return result;
		} else
			return super.locationStepString();
	}

	@Override
	public void setFunction(FunctionIdentifierExpression function) {
		this.functionExpression = function;
	}

	@Override
	protected void calculateConstantValueWork(SymbolicUniverse universe) {
		for (Expression arg : arguments)
			arg.calculateConstantValue(universe);
	}

}
