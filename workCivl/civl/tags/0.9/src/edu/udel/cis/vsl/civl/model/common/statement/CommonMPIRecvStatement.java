package edu.udel.cis.vsl.civl.model.common.statement;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.MPIModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BoundVariableExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DereferenceExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DotExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.IntegerLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.QuantifiedExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SubscriptExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.MPIRecvStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.model.common.expression.CommonIntegerLiteralExpression;

public class CommonMPIRecvStatement extends CommonStatement implements
		MPIRecvStatement {
	/* ************************* Instance Fields *************************** */
	private ArrayList<Expression> arguments;
	private LHSExpression lhs;
	private Expression guard;
	private VariableExpression rank;
	private MPIModelFactory modelFactory;

	/* ************************* Constructor ******************************* */
	public CommonMPIRecvStatement(CIVLSource civlsource, Location source,
			LHSExpression lhs, ArrayList<Expression> arguments,
			MPIModelFactory modelFactory) {
		super(civlsource, source);
		this.arguments = new ArrayList<Expression>(arguments);
		this.lhs = lhs;
		this.rank = modelFactory.rankVariable();
		this.modelFactory = modelFactory;
		guard = myGuard(civlsource);
		this.setGuard(guard);
	}

	/* ******************* Methods from MPIRecvStatement ******************* */
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
	public Expression getStatus() {

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
		CommonMPIRecvStatement newStatement = null;

		if (newGuard != null) {
			newStatement = new CommonMPIRecvStatement(this.getSource(),
					this.source(), this.lhs, this.arguments, this.modelFactory);
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
				newStatement = new CommonMPIRecvStatement(this.getSource(),
						this.source(), this.lhs, this.arguments,
						this.modelFactory);
				newStatement.setGuard(newGuard);
			}
		}

		return newStatement;
	}

	/* ************************* Methods from Object *********************** */
	public String toString() {
		if (this.getLeftHandSide() == null)
			return "MPI_Recv(" + this.arguments.get(0) + ", "
					+ this.arguments.get(1) + ", " + this.arguments.get(2)
					+ ", " + this.arguments.get(3) + ", "
					+ this.arguments.get(4) + ", " + this.arguments.get(5)
					+ ", " + this.arguments.get(6) + ")";
		else
			return this.lhs + " = MPI_Recv(" + this.arguments.get(0) + ", "
					+ this.arguments.get(1) + ", " + this.arguments.get(2)
					+ ", " + this.arguments.get(3) + ", "
					+ this.arguments.get(4) + ", " + this.arguments.get(5)
					+ ", " + this.arguments.get(6) + ")";
	}

	/* ************************ Private Methods ****************************** */
	private Expression myGuard(CIVLSource civlsource) {
		Expression commAddr = this.getCommunicator();
		DereferenceExpression comm = this.modelFactory.dereferenceExpression(
				civlsource, commAddr);
		Expression source = this.getMPISource();
		Expression tag = this.getTag();
		Expression nprocs = this.modelFactory.numberOfProcs();
		IntegerLiteralExpression MPI_ANY_SOURCE = new CommonIntegerLiteralExpression(
				civlsource, BigInteger.valueOf(-1));
		IntegerLiteralExpression MPI_ANY_TAG = new CommonIntegerLiteralExpression(
				civlsource, BigInteger.valueOf(-2));
		QuantifiedExpression checker = null;
		BinaryExpression result = null;
		Identifier boundVariable_i = this.modelFactory.identifier("i");
		CIVLType boundType = source.getExpressionType();
		BoundVariableExpression i = this.modelFactory.boundVariableExpression(
				civlsource, boundVariable_i, boundType);
		Identifier boundVariable_j = this.modelFactory.identifier("j");
		BoundVariableExpression j = this.modelFactory.boundVariableExpression(
				civlsource, boundVariable_j, boundType);
		IntegerLiteralExpression zero = this.modelFactory
				.integerLiteralExpression(BigInteger.ZERO);

		/* different situations come from various combination of tag and source */
		BinaryExpression isAnySource = this.modelFactory.binaryExpression(
				civlsource, BinaryExpression.BINARY_OPERATOR.EQUAL, source,
				MPI_ANY_SOURCE);
		BinaryExpression isAnyTag = this.modelFactory.binaryExpression(
				civlsource, BinaryExpression.BINARY_OPERATOR.EQUAL, tag,
				MPI_ANY_TAG);
		BinaryExpression isSpecSource = this.modelFactory.binaryExpression(
				civlsource, BinaryExpression.BINARY_OPERATOR.NOT_EQUAL, source,
				MPI_ANY_SOURCE);
		BinaryExpression isSpecTag = this.modelFactory.binaryExpression(
				civlsource, BinaryExpression.BINARY_OPERATOR.NOT_EQUAL, tag,
				MPI_ANY_TAG);
		BinaryExpression specSourceAndSpecTag = this.modelFactory
				.binaryExpression(civlsource,
						BinaryExpression.BINARY_OPERATOR.AND, isSpecSource,
						isSpecTag);
		BinaryExpression specSourceAndAnyTag = this.modelFactory
				.binaryExpression(civlsource,
						BinaryExpression.BINARY_OPERATOR.AND, isSpecSource,
						isAnyTag);
		BinaryExpression anySourceAndSpecTag = this.modelFactory
				.binaryExpression(civlsource,
						BinaryExpression.BINARY_OPERATOR.AND, isAnySource,
						isSpecTag);
		BinaryExpression anySourceAndAnyTag = this.modelFactory
				.binaryExpression(civlsource,
						BinaryExpression.BINARY_OPERATOR.AND, isAnySource,
						isAnyTag);

		/* specific source and specific tag */
		Expression queueLength = this.getQueueLengthAndMessages(civlsource,
				comm, source, rank)[0];
		Expression messages = this.getQueueLengthAndMessages(civlsource, comm,
				source, rank)[1];
		BinaryExpression leftRange = this.modelFactory.binaryExpression(
				civlsource, BinaryExpression.BINARY_OPERATOR.LESS_THAN_EQUAL,
				zero, i);
		BinaryExpression rightRange = this.modelFactory.binaryExpression(
				civlsource, BinaryExpression.BINARY_OPERATOR.LESS_THAN, i,
				queueLength);
		BinaryExpression restriction = this.modelFactory.binaryExpression(
				civlsource, BinaryExpression.BINARY_OPERATOR.AND, leftRange,
				rightRange);
		SubscriptExpression message = this.modelFactory.subscriptExpression(
				civlsource, (DotExpression) messages, i);
		DotExpression messageTag = this.modelFactory.dotExpression(civlsource,
				message, 2);
		BinaryExpression quantifiedExpression = this.modelFactory
				.binaryExpression(civlsource,
						BinaryExpression.BINARY_OPERATOR.EQUAL, messageTag, tag);
		checker = this.modelFactory.quantifiedExpression(civlsource,
				QuantifiedExpression.Quantifier.EXISTS, boundVariable_i,
				boundType, restriction, quantifiedExpression);
		result = this.modelFactory.binaryExpression(civlsource,
				BinaryExpression.BINARY_OPERATOR.AND, specSourceAndSpecTag,
				checker);
		/*
		 * specific source and ant tag. In this situation, the guard for this
		 * statement is the queue length of the specific queue must larger than
		 * 0
		 */
		BinaryExpression guard = this.modelFactory.binaryExpression(civlsource,
				BinaryExpression.BINARY_OPERATOR.LESS_THAN, zero, queueLength);
		guard = this.modelFactory.binaryExpression(civlsource,
				BinaryExpression.BINARY_OPERATOR.AND, specSourceAndAnyTag,
				guard);
		result = this.modelFactory.binaryExpression(civlsource,
				BinaryExpression.BINARY_OPERATOR.OR, result, guard);
		/*
		 * specific any source and specific tag. The guard for this statement is
		 * exits such a queue in all the message buffers of the process that has
		 * at least one message with the specific tag.
		 */;
		queueLength = this.getQueueLengthAndMessages(civlsource, comm, j, rank)[0];
		messages = this.getQueueLengthAndMessages(civlsource, comm, j, rank)[1];
		leftRange = this.modelFactory.binaryExpression(civlsource,
				BinaryExpression.BINARY_OPERATOR.LESS_THAN_EQUAL, zero, i);
		rightRange = this.modelFactory.binaryExpression(civlsource,
				BinaryExpression.BINARY_OPERATOR.LESS_THAN, i, queueLength);
		BinaryExpression restriction_i = this.modelFactory.binaryExpression(
				civlsource, BinaryExpression.BINARY_OPERATOR.AND, leftRange,
				rightRange);
		leftRange = this.modelFactory.binaryExpression(civlsource,
				BinaryExpression.BINARY_OPERATOR.LESS_THAN_EQUAL, zero, j);
		rightRange = this.modelFactory.binaryExpression(civlsource,
				BinaryExpression.BINARY_OPERATOR.LESS_THAN, j, nprocs);
		BinaryExpression restriction_j = this.modelFactory.binaryExpression(
				civlsource, BinaryExpression.BINARY_OPERATOR.AND, leftRange,
				rightRange);
		message = this.modelFactory.subscriptExpression(civlsource,
				(DotExpression) messages, i);
		messageTag = this.modelFactory.dotExpression(civlsource, message, 2);
		quantifiedExpression = this.modelFactory.binaryExpression(civlsource,
				BinaryExpression.BINARY_OPERATOR.EQUAL, messageTag, tag);
		checker = this.modelFactory.quantifiedExpression(civlsource,
				QuantifiedExpression.Quantifier.EXISTS, boundVariable_i,
				boundType, restriction_i, quantifiedExpression);
		checker = this.modelFactory.quantifiedExpression(civlsource,
				QuantifiedExpression.Quantifier.EXISTS, boundVariable_j,
				boundType, restriction_j, checker);
		guard = this.modelFactory.binaryExpression(civlsource,
				BinaryExpression.BINARY_OPERATOR.AND, anySourceAndSpecTag,
				checker);
		result = this.modelFactory.binaryExpression(civlsource,
				BinaryExpression.BINARY_OPERATOR.OR, result, guard);
		/*
		 * Any source and any tag. The guard of this kind of statements is there
		 * are at least one message in any queue of the message buffer of the
		 * process.
		 */
		quantifiedExpression = this.modelFactory.binaryExpression(civlsource,
				BinaryExpression.BINARY_OPERATOR.LESS_THAN, zero, queueLength);
		checker = this.modelFactory.quantifiedExpression(civlsource,
				QuantifiedExpression.Quantifier.EXISTS, boundVariable_j,
				boundType, restriction_j, quantifiedExpression);
		guard = this.modelFactory.binaryExpression(civlsource,
				BinaryExpression.BINARY_OPERATOR.AND, anySourceAndAnyTag,
				checker);
		result = this.modelFactory.binaryExpression(civlsource,
				BinaryExpression.BINARY_OPERATOR.OR, result, guard);
		return result;
	}

	private Expression[] getQueueLengthAndMessages(CIVLSource civlsource,
			Expression comm, Expression source, Expression rank) {
		DotExpression messageBuffer = this.modelFactory.dotExpression(
				civlsource, comm, 2);
		SubscriptExpression messageBufferRow = this.modelFactory
				.subscriptExpression(civlsource, messageBuffer, source);
		SubscriptExpression messageQueue = this.modelFactory
				.subscriptExpression(civlsource, messageBufferRow, rank);
		DotExpression queueLength = this.modelFactory.dotExpression(civlsource,
				messageQueue, 0);
		DotExpression messages = this.modelFactory.dotExpression(civlsource,
				messageQueue, 1);
		Expression[] result = { queueLength, messages };
		return result;
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
	public ArrayList<Expression> getArgumentsList() {
		return this.arguments;
	}

	@Override
	public StatementKind statementKind() {
		return StatementKind.MPI;
	}

	@Override
	public MPIStatementKind mpiStatementKind() {
		return MPIStatementKind.RECV;
	}

}
