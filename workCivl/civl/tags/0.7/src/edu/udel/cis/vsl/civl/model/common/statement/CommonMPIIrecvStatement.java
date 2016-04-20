package edu.udel.cis.vsl.civl.model.common.statement;

import java.util.ArrayList;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.MPIIrecvStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLHeapType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public class CommonMPIIrecvStatement extends CommonStatement implements
		MPIIrecvStatement {
	/* ************************* Instance Fields *************************** */
	private ArrayList<Expression> arguments;
	private LHSExpression lhs;

	/* ************************* Constructor ******************************* */
	public CommonMPIIrecvStatement(CIVLSource civlsource, Location source,
			LHSExpression lhs, ArrayList<Expression> arguments) {
		super(civlsource, source);
		this.arguments = new ArrayList<Expression>(arguments);
		this.lhs = lhs;
	}

	/* ******************* Methods from MPIIrecvStatement ****************** */
	@Override
	public Expression getBuffer() {
		return this.arguments.get(0);
	}

	@Override
	public Expression getCount() {
		return this.arguments.get(1);
	}

	@Override
	public Expression getDatatype() {
		return this.arguments.get(2);
	}

	@Override
	public Expression getMPISource() {
		return this.arguments.get(3);
	}

	@Override
	public Expression getTag() {
		return this.arguments.get(4);
	}

	@Override
	public Expression getCommunicator() {
		return this.arguments.get(5);
	}

	@Override
	public Expression getRequest() {
		return this.arguments.get(6);
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
		CommonMPIIrecvStatement newStatement = null;

		if (newGuard != null) {
			newStatement = new CommonMPIIrecvStatement(this.getSource(),
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
				newStatement = new CommonMPIIrecvStatement(this.getSource(),
						this.source(), this.lhs, this.arguments);
				newStatement.setGuard(newGuard);
			}
		}
		return newStatement;
	}

	/* ************************* Methods from Object *********************** */
	public String toString() {
		if (this.getLeftHandSide() == null)
			return "MPI_Irecv(" + this.arguments.get(0) + ", "
					+ this.arguments.get(1) + ", " + this.arguments.get(2)
					+ ", " + this.arguments.get(3) + ", "
					+ this.arguments.get(4) + ", " + this.arguments.get(5)
					+ ", " + this.arguments.get(6) + ")";
		else
			return this.lhs + " = MPI_Irecv(" + this.arguments.get(0) + ", "
					+ this.arguments.get(1) + ", " + this.arguments.get(2)
					+ ", " + this.arguments.get(3) + ", "
					+ this.arguments.get(4) + ", " + this.arguments.get(5)
					+ ", " + this.arguments.get(6) + ")";
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope,
			CIVLHeapType heapType, CIVLType commType) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Set<Variable> variableAddressedOf(CIVLHeapType heapType,
			CIVLType commType) {
		// TODO Auto-generated method stub
		return null;
	}
}
