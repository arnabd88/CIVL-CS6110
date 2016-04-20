package edu.udel.cis.vsl.civl.model.common.statement;

import java.util.ArrayList;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.MPIIsendStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public class CommonMPIIsendStatement extends CommonStatement implements
		MPIIsendStatement {
	/* ************************* Instance Fields *************************** */
	private ArrayList<Expression> arguments;
	private LHSExpression lhs;

	/* ************************* Constructor ******************************* */
	public CommonMPIIsendStatement(CIVLSource civlsource, Location source,
			LHSExpression lhs, ArrayList<Expression> arguments) {
		super(civlsource, source);
		this.arguments = new ArrayList<Expression>(arguments);
		this.lhs = lhs;
	}

	/* ******************* Methods from MPIIsendStatement ****************** */
	@Override
	public Expression getBuffer() {
		return arguments.get(0);
	}

	@Override
	public Expression getCount() {
		return arguments.get(1);
	}

	@Override
	public Expression getDatatype() {
		return arguments.get(2);
	}

	@Override
	public Expression getDestination() {
		return arguments.get(3);
	}

	@Override
	public Expression getTag() {
		return arguments.get(4);
	}

	@Override
	public Expression getCommunicator() {
		return arguments.get(5);
	}

	@Override
	public Expression getRequest() {
		return arguments.get(6);
	}

	@Override
	public LHSExpression getLeftHandSide() {
		return this.lhs;
	}

	@Override
	public void setLeftHandSide(LHSExpression lhs) {
		this.lhs = lhs;
	}

	/* ************************* Methods from Statement ******************** */
	@Override
	public Statement replaceWith(ConditionalExpression oldExpression,
			Expression newExpression) {
		Expression newGuard = this.guardReplaceWith(oldExpression,
				newExpression);
		CommonMPIIsendStatement newStatement = null;

		if (newGuard != null) {
			newStatement = new CommonMPIIsendStatement(this.getSource(),
					this.source(), this.lhs, this.arguments);
			newStatement.setGuard(newGuard);
		} else {
			ArrayList<Expression> newArgs = new ArrayList<Expression>();
			int number = this.arguments.size();
			Expression newArg;
			boolean hasNewArg = false;

			for (int i = 0; i < number; i++) {
				if (hasNewArg) {
					newArgs.add(this.arguments.get(i));
				} else {
					newArg = this.arguments.get(i).replaceWith(oldExpression,
							newExpression);

					if (newArg != null) {
						newArgs.add(newArg);
						hasNewArg = true;
					} else {
						newArgs.add(this.arguments.get(i));
					}
				}
			}
			if (hasNewArg) {
				newStatement = new CommonMPIIsendStatement(this.getSource(),
						this.source(), this.lhs, this.arguments);
				newStatement.setGuard(newGuard);
			}
		}
		return newStatement;
	}

	/* ************************* Methods from Object *********************** */
	public String toString() {
		if (this.getLeftHandSide() == null) {
			return "MPI_Isend(" + this.arguments.get(0) + ", "
					+ this.arguments.get(1) + ", " + this.arguments.get(2)
					+ ", " + this.arguments.get(3) + ", "
					+ this.arguments.get(4) + ", " + this.arguments.get(5)
					+ this.arguments.get(6) + ")";
		} else {
			return this.lhs + " = MPI_Isend(" + this.arguments.get(0) + ", "
					+ this.arguments.get(1) + ", " + this.arguments.get(2)
					+ ", " + this.arguments.get(3) + ", "
					+ this.arguments.get(4) + ", " + this.arguments.get(5)
					+ this.arguments.get(6) + ")";
		}
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public StatementKind statementKind() {
		return StatementKind.MPI;
	}

	@Override
	public MPIStatementKind mpiStatementKind() {
		return MPIStatementKind.ISEND;
	}

}
