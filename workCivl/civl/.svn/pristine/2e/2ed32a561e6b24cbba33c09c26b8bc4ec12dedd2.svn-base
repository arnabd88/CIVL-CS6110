package edu.udel.cis.vsl.civl.library.mpi;

import java.util.List;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryEvaluator;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.SystemFunctionCallExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;

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
	 * Evaluate {@link SystemFunctionCallExpression}s whose function is defined
	 * in MPI library.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process.
	 * @param expression
	 *            The {@link SystemFunctionCallExpression}
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	public Evaluation evaluateMPISystemFunctionCallExpression(State state,
			int pid, String process, SystemFunctionCallExpression expression)
			throws UnsatisfiablePathConditionException {
		CallOrSpawnStatement call = expression.callStatement();
		List<Expression> arguments = call.arguments();

		switch (call.function().name().name()) {
		case "$mpi_isRecvBufEmpty":
			return evaluateRecvBufEmptyExpression(state, pid, process,
					arguments.get(0), (VariableExpression) arguments.get(1),
					call.getSource());
		case "$mpi_isSendBufEmpty":
		}
		return null;
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
			String process, Expression arg0, VariableExpression MPIComm,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluator.evaluate(state, pid, MPIComm);
		SymbolicExpression MPICommVal;
		NumericExpression src;
		SymbolicExpression msgBuffers, p2pBuf, colBuf, p2p, col;
		BooleanExpression p2pClaim, colClaim;
		Pair<NumericExpression, NumericExpression> place_queueId;
		int queueID;

		state = eval.state;
		MPICommVal = eval.value;
		place_queueId = getPlaceAndQueueIDFromMPIComm(state, pid, process,
				MPIComm, MPICommVal, source);
		eval = evaluator.evaluate(state, pid, arg0);
		state = eval.state;
		src = (NumericExpression) eval.value;
		// queueID is created by CIVL and won't be symbolic
		queueID = ((IntegerNumber) universe
				.extractNumber((NumericExpression) place_queueId.right))
				.intValue();
		msgBuffers = stateFactory.peekCollectiveSnapshotsEntry(state, queueID)
				.getMsgBuffers();
		p2p = universe.arrayRead(msgBuffers, zero);
		p2pBuf = universe.arrayRead(universe.arrayRead(p2p, src),
				place_queueId.left);
		col = universe.arrayRead(msgBuffers, one);
		colBuf = universe.arrayRead(universe.arrayRead(col, src),
				place_queueId.left);
		p2pClaim = universe
				.equals(universe.tupleRead(p2pBuf, zeroObject), zero);
		colClaim = universe
				.equals(universe.tupleRead(colBuf, zeroObject), zero);
		return new Evaluation(state, universe.and(p2pClaim, colClaim));
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
}
