package edu.udel.cis.vsl.civl.model.common.statement;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.AbstractFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.model.common.location.CommonLocation.AtomicKind;

/**
 * A function call or spawn. Either of the form f(x) or else v=f(x).
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonCallStatement extends CommonStatement implements
		CallOrSpawnStatement {

	private boolean isCall;

	private LHSExpression lhs = null;

	private CIVLFunction function;

	private List<Expression> arguments;

	/**
	 * A function call. Either of the form f(x) or else v=f(x).
	 * 
	 * @param source
	 *            The source location for this call statement.
	 * @param isCall
	 *            is this a call statement (not fork)?
	 * @param function
	 *            The function.
	 * @param arguments
	 *            The arguments to the function.
	 */
	public CommonCallStatement(CIVLSource civlSource, Location source,
			boolean isCall, CIVLFunction function, List<Expression> arguments) {
		super(civlSource, source);
		this.isCall = isCall;
		this.function = function;
		this.arguments = arguments;
	}

	/**
	 * A function call.
	 * 
	 * @param source
	 *            The source location for this call statement.
	 * @param lhs
	 *            The (optional) left hand side expression. Used when the call
	 *            statement is also an assignment. Null if not applicable.
	 * @param function
	 *            The function.
	 * @param arguments
	 *            The arguments to the function.
	 */
	public CommonCallStatement(CIVLSource civlSource, Location source,
			LHSExpression lhs, CIVLFunction function, List<Expression> arguments) {
		super(civlSource, source);
		this.lhs = lhs;
		this.function = function;
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
		return function;
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
	 * @param function
	 *            The function being called.
	 */
	@Override
	public void setFunction(CIVLFunction function) {
		this.function = function;
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
		String result = function.name().name();
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
					this.source(), lhs, this.function, this.arguments);
			newStatement.setGuard(newGuard);
			newStatement.isCall = this.isCall;
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
						this.source(), lhs, this.function, newArgs);
				newStatement.setGuard(this.guard());
				newStatement.isCall = this.isCall;
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

			for (Expression argument : arguments) {
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

			for (Expression argument : arguments) {
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
		return this.function.isSystem();
	}

	@Override
	public String toStepString(AtomicKind atomicKind, int atomCount,
			boolean atomicLockVarChanged) {
		String targetString;
		String result = "  " + source().id() + "->";

		if (isCall() && !isSystemCall()) {
			if (!(function instanceof AbstractFunction)) {
				targetString = Integer.toString(function.startLocation().id());
			} else {
				return super.toStepString(atomicKind, atomCount,
						atomicLockVarChanged);
			}
		} else
			return super.toStepString(atomicKind, atomCount,
					atomicLockVarChanged);
		result += targetString + ": ";
		switch (atomicKind) {
		case ATOMIC_ENTER:
			if (atomicLockVarChanged) {
				result += toString() + " ";
			} else
				result += "ENTER_ATOMIC (atomicCount++) ";
			result += Integer.toString(atomCount - 1);
			break;
		case ATOMIC_EXIT:
			if (atomicLockVarChanged) {
				result += toString() + " ";
			} else
				result += "LEAVE_ATOMIC (atomicCount--) ";
			result += Integer.toString(atomCount);
			break;
		case ATOM_ENTER:
			result += toString() + " ";
			result += Integer.toString(atomCount - 1);
			break;
		case ATOM_EXIT:
			result += toString() + " ";
			result += Integer.toString(atomCount);
			break;
		default:
			result += toString();
		}
		if (getSource() != null)
			result += " at " + getSource().getSummary();
		else
			result += " at " + source().getSource().getSummary();
		result += ";\n";
		return result;
	}

}
