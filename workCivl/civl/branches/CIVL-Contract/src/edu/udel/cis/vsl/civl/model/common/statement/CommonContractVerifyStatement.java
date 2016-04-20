package edu.udel.cis.vsl.civl.model.common.statement;

import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.FunctionIdentifierExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.ContractVerifyStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;

public class CommonContractVerifyStatement extends CommonStatement implements
		ContractVerifyStatement {

	private FunctionIdentifierExpression functionExpression;

	private List<Expression> arguments;

	public CommonContractVerifyStatement(CIVLSource civlSource, Scope hscope,
			Scope lscope, Location source,
			FunctionIdentifierExpression functionExpression,
			List<Expression> arguments, Expression guard) {
		super(civlSource, hscope, lscope, source, guard);
		this.functionExpression = functionExpression;
		this.arguments = arguments;
	}

	@Override
	public Statement replaceWith(ConditionalExpression oldExpression,
			Expression newExpression) {
		List<Expression> newArguments = new LinkedList<>();

		if (arguments != null) {
			for (Expression arg : arguments) {
				newArguments.add(arg.replaceWith(oldExpression, newExpression));
			}
			this.arguments = newArguments;
		}
		return new CommonContractVerifyStatement(this.getSource(),
				this.statementScope, this.lowestScope, this.source(),
				functionExpression, arguments, guard());
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		Set<Variable> vars = new HashSet<Variable>();

		vars.addAll(functionExpression.variableAddressedOf(scope));
		for (Expression arg : arguments) {
			Set<Variable> argResults = arg.variableAddressedOf(scope);
			if (argResults != null)
				vars.addAll(argResults);
		}
		return vars;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		Set<Variable> vars = new HashSet<Variable>();

		vars.addAll(functionExpression.variableAddressedOf());
		for (Expression arg : arguments) {
			Set<Variable> argResults = arg.variableAddressedOf();
			if (argResults != null)
				vars.addAll(argResults);
		}
		return vars;
	}

	@Override
	public StatementKind statementKind() {
		return StatementKind.CONTRACT_VERIFY;
	}

	@Override
	public CIVLFunction function() {
		return functionExpression.function();
	}

	@Override
	public List<Expression> arguments() {
		return arguments;
	}

	@Override
	public void setFunction(FunctionIdentifierExpression function) {
		this.functionExpression = function;
	}

	@Override
	public void setArguments(List<Expression> arguments) {
		this.arguments = arguments;
	}

	@Override
	public boolean isSystemCall() {
		CIVLFunction function = this.function();

		if (function != null && function.isSystemFunction()) {
			return true;
		}
		return false;
	}

	@Override
	public Expression functionExpression() {
		return functionExpression;
	}

	@Override
	protected void calculateConstantValueWork(SymbolicUniverse universe) {
		functionExpression.calculateConstantValue(universe);
		for (Expression arg : arguments) {
			arg.calculateConstantValue(universe);
		}
	}

	@Override
	public String toString() {
		StringBuffer buffer = new StringBuffer();
		Iterator<Expression> argIter = arguments.iterator();

		buffer.append("$contractVerify " + functionExpression.toString() + "(");
		if (argIter.hasNext())
			buffer.append(argIter.next());
		while (argIter.hasNext()) {
			buffer.append(" ," + argIter.next());
		}
		return buffer.toString();
	}
}
