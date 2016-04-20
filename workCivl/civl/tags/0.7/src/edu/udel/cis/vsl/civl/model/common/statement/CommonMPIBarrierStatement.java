package edu.udel.cis.vsl.civl.model.common.statement;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.MPIBarrierStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLHeapType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public class CommonMPIBarrierStatement extends CommonStatement implements
		MPIBarrierStatement {
	/* ************************* Instance Fields *************************** */
	private Expression comm;
	private LHSExpression lhs;

	/* ************************* Constructor ******************************* */
	public CommonMPIBarrierStatement(CIVLSource civlsource, Location source,
			LHSExpression lhs, Expression comm) {
		super(civlsource, source);
		this.comm = comm;
		this.lhs = lhs;
	}

	/* ******************* Methods from MPIBarrierStatement **************** */
	@Override
	public Expression getCommunicator() {
		return this.comm;
	}

	@Override
	public LHSExpression getLeftHandSide() {
		return this.lhs;
	}

	@Override
	public void setLeftHandSide(LHSExpression lhs) {
		this.lhs = lhs;
	}

	/* ******************* Methods from Statement ************************** */
	@Override
	public Statement replaceWith(ConditionalExpression oldExpression,
			Expression newExpression) {
		Expression newGuard = this.guardReplaceWith(oldExpression,
				newExpression);
		CommonMPIBarrierStatement newStatement = null;

		if (newGuard != null) {
			newStatement = new CommonMPIBarrierStatement(this.getSource(),
					this.source(), this.lhs, this.comm);
			newStatement.setGuard(newGuard);
		} else {
			Expression newComm = comm.replaceWith(oldExpression, newExpression);
			if (newComm != null) {
				newStatement = new CommonMPIBarrierStatement(this.getSource(),
						this.source(), this.lhs, newComm);
			} else
				newStatement = new CommonMPIBarrierStatement(this.getSource(),
						this.source(), this.lhs, this.comm);
		}
		return newStatement;
	}

	/* ************************* Methods from Object *********************** */
	public String toString() {
		if (this.getLeftHandSide() == null) {
			return "MPI_Barrier(" + this.getCommunicator() + ")";
		} else {
			return this.lhs + " = MPI_Barrier(" + this.getCommunicator() + ")";
		}
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
