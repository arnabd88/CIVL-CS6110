package edu.udel.cis.vsl.civl.library.mpi;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.comm.LibcommExecutor;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryEvaluator;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.contract.MPICollectiveBehavior;
import edu.udel.cis.vsl.civl.model.IF.contract.MPICollectiveBehavior.MPICommunicationPattern;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression.ExpressionKind;
import edu.udel.cis.vsl.civl.model.IF.expression.MPIContractExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.MPIContractExpression.MPI_CONTRACT_EXPRESSION_KIND;
import edu.udel.cis.vsl.civl.model.IF.expression.SystemFunctionCallExpression;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.CollectiveSnapshotsEntry;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.civl.util.IF.Triple;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Number;

;

public class LibmpiEvaluator extends BaseLibraryEvaluator implements
		LibraryEvaluator {
	public static final int p2pCommField = 0;
	public static final int colCommField = 1;
	public static final int IDField = 4;

	public LibmpiEvaluator(String name, Evaluator evaluator,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer, CIVLConfiguration civlConfig,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, evaluator, modelFactory, symbolicUtil, symbolicAnalyzer,
				civlConfig, libEvaluatorLoader);

	}

	/**
	 * Evaluate the {@link SystemFunctionCallExpression} $mpi_isRecvBufEmpty(int
	 * src, MPI_Comm comm). Note: the second argument "comm" is added by CIVL
	 * model.
	 * 
	 * @param state
	 *            The state on where the evaluation happens
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param arg0
	 *            The expression of the first argument
	 * @param MPIComm
	 *            The expression of the second argument
	 * @param source
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateRecvBufEmptyExpression(State state, int pid,
			String process, Expression arg0, Expression MPIComm,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluator.evaluate(state, pid, MPIComm);
		SymbolicExpression MPICommVal;
		NumericExpression src;
		SymbolicExpression msgBuffers, p2pBuf, colBuf, p2p, col;
		BooleanExpression p2pClaim, colClaim;
		Pair<NumericExpression, NumericExpression> place_queueId;
		int queueID;

		// TODO: optimize code
		state = eval.state;
		MPICommVal = eval.value;
		place_queueId = getPlaceAndQueueIDFromMPIComm(state, pid, process,
				MPIComm, MPICommVal, source);
		if (!arg0.expressionKind().equals(ExpressionKind.WILDCARD)) {
			eval = evaluator.evaluate(state, pid, arg0);
			state = eval.state;
			src = (NumericExpression) eval.value;
			// queueID is created by CIVL and won't be symbolic
			queueID = ((IntegerNumber) universe
					.extractNumber((NumericExpression) place_queueId.right))
					.intValue();
			msgBuffers = stateFactory.peekCollectiveSnapshotsEntry(state,
					queueID).getMsgBuffers();
			p2p = universe.arrayRead(msgBuffers, zero);
			p2pBuf = universe.arrayRead(universe.arrayRead(p2p, src),
					place_queueId.left);
			col = universe.arrayRead(msgBuffers, one);
			colBuf = universe.arrayRead(universe.arrayRead(col, src),
					place_queueId.left);
			p2pClaim = universe.equals(universe.tupleRead(p2pBuf, zeroObject),
					zero);
			colClaim = universe.equals(universe.tupleRead(colBuf, zeroObject),
					zero);
			return new Evaluation(state, universe.and(p2pClaim, colClaim));
		} else {
			CollectiveSnapshotsEntry entry;
			int nprocs;
			BooleanExpression claim = universe.trueExpression();

			queueID = ((IntegerNumber) universe
					.extractNumber((NumericExpression) place_queueId.right))
					.intValue();
			entry = stateFactory.peekCollectiveSnapshotsEntry(state, queueID);
			nprocs = entry.numInvolvedProcesses();
			for (int i = 0; i < nprocs; i++) {
				NumericExpression concSrc = universe.integer(i);

				msgBuffers = stateFactory.peekCollectiveSnapshotsEntry(state,
						queueID).getMsgBuffers();
				p2p = universe.arrayRead(msgBuffers, zero);
				p2pBuf = universe.arrayRead(universe.arrayRead(p2p, concSrc),
						place_queueId.left);
				col = universe.arrayRead(msgBuffers, one);
				colBuf = universe.arrayRead(universe.arrayRead(col, concSrc),
						place_queueId.left);
				p2pClaim = universe.equals(
						universe.tupleRead(p2pBuf, zeroObject), zero);
				colClaim = universe.equals(
						universe.tupleRead(colBuf, zeroObject), zero);
				claim = universe.and(universe.and(claim, p2pClaim), colClaim);
			}
			return new Evaluation(state, claim);
		}
	}

	// TODO: better to be combined with evaluateRecvBufEmptyExpression
	private Evaluation evaluateSendBufEmptyExpression(State state, int pid,
			String process, Expression arg0, Expression MPIComm,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluator.evaluate(state, pid, MPIComm);
		SymbolicExpression MPICommVal;
		NumericExpression dest;
		SymbolicExpression msgBuffers, p2pBuf, colBuf, p2p, col;
		BooleanExpression p2pClaim, colClaim;
		Pair<NumericExpression, NumericExpression> place_queueId;
		int queueID;

		// TODO: optimize code
		state = eval.state;
		MPICommVal = eval.value;
		place_queueId = getPlaceAndQueueIDFromMPIComm(state, pid, process,
				MPIComm, MPICommVal, source);
		if (!arg0.expressionKind().equals(ExpressionKind.WILDCARD)) {
			eval = evaluator.evaluate(state, pid, arg0);
			state = eval.state;
			dest = (NumericExpression) eval.value;
			// queueID is created by CIVL and won't be symbolic
			queueID = ((IntegerNumber) universe
					.extractNumber((NumericExpression) place_queueId.right))
					.intValue();
			msgBuffers = stateFactory.peekCollectiveSnapshotsEntry(state,
					queueID).getMsgBuffers();
			p2p = universe.arrayRead(msgBuffers, zero);
			p2pBuf = universe.arrayRead(
					universe.arrayRead(p2p, place_queueId.left), dest);
			col = universe.arrayRead(msgBuffers, one);
			colBuf = universe.arrayRead(
					universe.arrayRead(col, place_queueId.left), dest);
			p2pClaim = universe.equals(universe.tupleRead(p2pBuf, zeroObject),
					zero);
			colClaim = universe.equals(universe.tupleRead(colBuf, zeroObject),
					zero);
			return new Evaluation(state, universe.and(p2pClaim, colClaim));
		} else {
			CollectiveSnapshotsEntry entry;
			int nprocs;
			BooleanExpression claim = universe.trueExpression();

			queueID = ((IntegerNumber) universe
					.extractNumber((NumericExpression) place_queueId.right))
					.intValue();
			entry = stateFactory.peekCollectiveSnapshotsEntry(state, queueID);
			nprocs = entry.numInvolvedProcesses();
			for (int i = 0; i < nprocs; i++) {
				NumericExpression concDest = universe.integer(i);

				msgBuffers = stateFactory.peekCollectiveSnapshotsEntry(state,
						queueID).getMsgBuffers();
				p2p = universe.arrayRead(msgBuffers, zero);
				p2pBuf = universe.arrayRead(
						universe.arrayRead(p2p, place_queueId.left), concDest);
				col = universe.arrayRead(msgBuffers, one);
				colBuf = universe.arrayRead(
						universe.arrayRead(col, place_queueId.left), concDest);
				p2pClaim = universe.equals(
						universe.tupleRead(p2pBuf, zeroObject), zero);
				colClaim = universe.equals(
						universe.tupleRead(colBuf, zeroObject), zero);
				claim = universe.and(universe.and(claim, p2pClaim), colClaim);
			}
			return new Evaluation(state, claim);
		}
	}

	/**
	 * A helper function: Returns the place field and the message buffer field
	 * by accessing through a $comm handle.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param MPIComm
	 *            The Expression of the MPI communicator handle
	 * @param MPICommVal
	 *            The Symbolic Expression of the MPI communicator handle
	 * @param source
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Pair<NumericExpression, NumericExpression> getPlaceAndQueueIDFromMPIComm(
			State state, int pid, String process, Expression MPIComm,
			SymbolicExpression MPICommVal, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		Evaluation eval;
		SymbolicExpression p2pComm, p2pCommHandle;
		NumericExpression place, queueID;

		queueID = (NumericExpression) universe.tupleRead(MPICommVal,
				universe.intObject(4));
		p2pCommHandle = universe.tupleRead(MPICommVal, zeroObject);
		eval = evaluator.dereference(source, state, process, MPIComm,
				p2pCommHandle, false);
		state = eval.state;
		p2pComm = eval.value;
		place = (NumericExpression) universe.tupleRead(p2pComm, zeroObject);
		return new Pair<>(place, queueID);
	}

	/**************************** Contract section ****************************/
	/**
	 * Evaluates an {@link MPIContractExpression}.
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The PID of the process.
	 * @param process
	 *            The String identifier of the process.
	 * @param expression
	 *            The MPIContractExpression
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	public Evaluation evaluateMPIContractExpression(State state, int pid,
			String process, MPIContractExpression expression)
			throws UnsatisfiablePathConditionException {
		MPI_CONTRACT_EXPRESSION_KIND mpiContractKind = expression
				.mpiContractKind();

		switch (mpiContractKind) {
		case MPI_EMPTY_IN:
			return this.evaluateMPIEmptyExpression(state, pid, process,
					expression, false);
		case MPI_EMPTY_OUT:
			return this.evaluateMPIEmptyExpression(state, pid, process,
					expression, true);
		case MPI_AGREE:
			return this.evaluateMPIAgreeExpression(state, pid, process,
					expression);
		case MPI_EQUALS:
			return this.evaluateMPIEqualsExpression(state, pid, process,
					expression);
		default:
			// TODO; to be continue
			throw new CIVLInternalException("Unreachable",
					expression.getSource());
		}
	}

	/**
	 * Evaluates \mpi_empty_in(int src) / \mpi_empty_out(int dest) expression
	 * (both accept wild card argument which means for all sources (src) or
	 * destinations (dest)).
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String of the process identifier
	 * @param expression
	 *            The {@link MPIContractExpression} expression
	 * @param isOut
	 *            flag indicates weather it's a \mpi_empty_out or \mpi_empty_in
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateMPIEmptyExpression(State state, int pid,
			String process, MPIContractExpression expression, boolean isOut)
			throws UnsatisfiablePathConditionException {
		Expression communicator = expression.communicator();
		Expression argument = expression.arguments()[0];

		if (isOut)
			return evaluateSendBufEmptyExpression(state, pid, process,
					argument, communicator, expression.getSource());
		else
			return evaluateRecvBufEmptyExpression(state, pid, process,
					argument, communicator, expression.getSource());
	}

	/**
	 * Evaluates an MPI agree expression: The expression will be simply
	 * evaluated to true because all \mpi_agree expressions are collected and
	 * processed when inferring a state.
	 * 
	 * @param state
	 * @param pid
	 * @param process
	 * @param expression
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateMPIAgreeExpression(State state, int pid,
			String process, MPIContractExpression expression)
			throws UnsatisfiablePathConditionException {
		return new Evaluation(state, universe.trueExpression());
	}

	/**
	 * Evaluates an MPI_EQUALS expression, it compares each elements of the
	 * given two memory objects. Currently it ignores the datatype checking (but
	 * not necessary if objects are checked as equal).
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param expression
	 *            The MPI_EQUALS expression.
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateMPIEqualsExpression(State state, int pid,
			String process, MPIContractExpression expression)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression values[] = new SymbolicExpression[4];
		Evaluation eval;
		SymbolicExpression result0, result1;
		BooleanExpression result;
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		int count;
		Number countNum;
		CIVLSource source = expression.getSource();

		for (int i = 0; i < 4; i++) {
			eval = evaluator.evaluate(state, pid, expression.arguments()[i]);
			state = eval.state;
			values[i] = eval.value;
		}
		countNum = reasoner.extractNumber((NumericExpression) values[1]);
		if (countNum == null)
			throw new CIVLInternalException("Value of expression: "
					+ expression.arguments()[2]
					+ "are expecting to be elaborated to concrete",
					expression.arguments()[2].getSource());
		count = ((IntegerNumber) countNum).intValue();
		// Offset = 0:
		eval = evaluator.dereference(source, state, process,
				expression.arguments()[0], values[0], false);
		result0 = eval.value;
		eval = evaluator.dereference(source, state, process,
				expression.arguments()[3], values[3], false);
		result1 = eval.value;
		result = universe.equals(result0, result1);
		// Offset > 0:
		for (int i = 1; i < count; i++) {
			eval = evaluator.evaluatePointerAdd(state, process, values[0],
					universe.integer(i), false, source).left;
			eval = evaluator.dereference(expression.getSource(), state,
					process, expression.arguments()[0], eval.value, false);
			result0 = eval.value;
			eval = evaluator.evaluatePointerAdd(state, process, values[3],
					universe.integer(i), false, source).left;
			eval = evaluator.dereference(expression.getSource(), state,
					process, expression.arguments()[3], eval.value, false);
			result1 = eval.value;
			result = universe.and(result, universe.equals(result0, result1));
		}
		return new Evaluation(state, result);
	}

	// TODO: insert snapshots:
	/**
	 * This method is responsible for a set of initialization works for an MPI
	 * collective behavior block. It assigns \mpi_comm_rank and \mpi_comm_size
	 * and creates or inserts snapshots (TODO) for collective properties.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param behavior
	 *            The {@link MPICollectiveBehavior}
	 * @param function
	 *            The verifying function who owns the contracts
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	public Triple<State, SymbolicExpression, SymbolicExpression> deriveMPICollectiveBlockTitle(
			State state, int pid, String process,
			MPICollectiveBehavior behavior, CIVLFunction function)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression commHandle, comm, gcommHandle, gcomm, place;
		NumericExpression nprocs;
		SymbolicExpression newBuffer;
		Evaluation eval;
		Scope verifyingFunctionOuter = function.outerScope();
		Expression communicator = behavior.communicator();

		eval = evaluator.evaluate(state, pid, communicator);
		state = eval.state;
		if (behavior.mpiCommunicationPattern() == MPICommunicationPattern.P2P)
			commHandle = universe.tupleRead(eval.value,
					universe.intObject(p2pCommField));
		else
			commHandle = universe.tupleRead(eval.value,
					universe.intObject(colCommField));
		eval = evaluator.dereference(communicator.getSource(), state, process,
				communicator, commHandle, false);
		state = eval.state;
		comm = eval.value;
		gcommHandle = universe.tupleRead(comm, oneObject);
		place = universe.tupleRead(comm, zeroObject);
		eval = evaluator.dereference(communicator.getSource(), state, process,
				communicator, gcommHandle, false);
		state = eval.state;
		gcomm = eval.value;
		nprocs = (NumericExpression) universe.tupleRead(gcomm, zeroObject);
		// clear buffer:
		newBuffer = LibcommExecutor.newGcommBuffer(universe, model,
				symbolicUtil, state.getPathCondition(), nprocs);
		gcomm = universe.tupleWrite(gcomm, this.threeObject, newBuffer);
		// assign \mpi_comm_rank and \mpi_comm_nprocs if they exist:
		if (verifyingFunctionOuter.containsVariable("\\mpi_comm_rank")) {
			Variable var = verifyingFunctionOuter.variable("\\mpi_comm_rank");

			state = stateFactory.setVariable(state, var, pid, place);
		}
		if (verifyingFunctionOuter.containsVariable("\\mpi_comm_size")) {
			Variable var = verifyingFunctionOuter.variable("\\mpi_comm_size");

			state = stateFactory.setVariable(state, var, pid, nprocs);
		}
		return new Triple<>(state, gcommHandle, gcomm);
	}
}
