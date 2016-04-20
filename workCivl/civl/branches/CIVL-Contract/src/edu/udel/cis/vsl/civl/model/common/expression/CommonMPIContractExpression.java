package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.MPIContractExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public class CommonMPIContractExpression extends CommonExpression implements
		MPIContractExpression {
	private MPI_CONTRACT_EXPRESSION_KIND mpiContractKind;

	private Expression[] arguments;

	private Expression communicator;

	public CommonMPIContractExpression(CIVLSource source, Scope hscope,
			Scope lscope, CIVLType type, MPI_CONTRACT_EXPRESSION_KIND kind,
			Expression communicator, Expression[] arguments) {
		super(source, hscope, lscope, type);
		this.communicator = communicator;
		this.arguments = arguments;
		this.mpiContractKind = kind;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.MPI_CONTRACT_EXPRESSION;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		Set<Variable> set = communicator.variableAddressedOf(scope);

		for (int i = 0; i < arguments.length; i++)
			set.addAll(arguments[i].variableAddressedOf(scope));
		return set;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		Set<Variable> set = communicator.variableAddressedOf();

		for (int i = 0; i < arguments.length; i++)
			set.addAll(arguments[i].variableAddressedOf());
		return set;
	}

	@Override
	public MPI_CONTRACT_EXPRESSION_KIND mpiContractKind() {
		return mpiContractKind;
	}

	@Override
	public Expression communicator() {
		return communicator;
	}

	@Override
	public Expression[] arguments() {
		return arguments;
	}

	@Override
	protected boolean expressionEquals(Expression expression) {
		if (expression instanceof MPIContractExpression) {
			MPIContractExpression mpiConcExpr = (MPIContractExpression) expression;

			if (mpiConcExpr.mpiContractKind().equals(mpiContractKind)) {
				if (mpiConcExpr.communicator().equals(communicator)) {
					if (mpiConcExpr.arguments().length == arguments.length) {
						Expression[] otherArgs = mpiConcExpr.arguments();
						for (int i = 0; i < arguments.length; i++)
							if (!otherArgs[i].equals(arguments[i]))
								return false;
						return true;
					}
				}
			}
		}
		return false;
	}

	@Override
	public String toString() {
		StringBuffer result = new StringBuffer();

		result.append(mpiContractKind + " (");
		result.append(arguments[0]);
		for (int i = 1; i < this.arguments.length; i++) {
			result.append(", " + arguments[i]);
		}
		result.append(")");
		return result.toString();
	}

}
