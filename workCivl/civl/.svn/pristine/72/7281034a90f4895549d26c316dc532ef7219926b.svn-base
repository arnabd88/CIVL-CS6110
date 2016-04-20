package edu.udel.cis.vsl.civl.model.common.statement;

import java.util.ArrayList;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.MPIWaitStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;

public class CommonMPIWaitStatement extends CommonStatement implements
		MPIWaitStatement {
	/* ************************* Instance Fields *************************** */
	private ArrayList<Expression> arguments;
	private LHSExpression lhs;

	/* ************************* Constructor ******************************* */
	public CommonMPIWaitStatement(CIVLSource civlsource, Location source,
			LHSExpression lhs, ArrayList<Expression> arguments) {
		super(civlsource, source);
		this.lhs = lhs;
		this.arguments = new ArrayList<Expression>(arguments);
	}

	/* ******************* Methods from MPIWaitStatement ******************* */
	@Override
	public Expression getRequest() {
		return this.arguments.get(0);
	}

	@Override
	public Expression getStatus() {
		return this.arguments.get(1);
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
		CommonMPIWaitStatement newStatement = null;

		if (newGuard != null) {
			newStatement = new CommonMPIWaitStatement(this.getSource(),
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
					} else
						newArgs.add(this.arguments.get(i));
				}
			}
			if (hasNewArg) {
				newStatement = new CommonMPIWaitStatement(this.getSource(),
						this.source(), this.lhs, this.arguments);
				newStatement.setGuard(newGuard);
			}
		}

		return newStatement;
	}

	/* ************************* Methods from Object *********************** */
	public String toString() {
		if (this.getLeftHandSide() == null) {
			return "MPI_Wait(" + this.arguments.get(0) + ", "
					+ this.arguments.get(1) + ")";
		} else {
			return this.lhs + " = MPI_Wait(" + this.arguments.get(0) + ", "
					+ this.arguments.get(1) + ")";
		}
	}
}
