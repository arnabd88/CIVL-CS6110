package edu.udel.cis.vsl.civl.state.IF;

import java.util.List;

import edu.udel.cis.vsl.civl.model.IF.contract.FunctionContract.ContractKind;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.state.common.immutable.ImmutableCollectiveSnapshotsEntry;
import edu.udel.cis.vsl.civl.state.common.immutable.ImmutableMonoState;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * This class represents one complete entry for the snapshots queue used in
 * collective assertion checking.
 * 
 * Once a entry created, it stores the information of the communicator and
 * corresponds to the communicator.
 * 
 * Every process will add themselves into one entry once they reach the
 * corresponding "collective assertion".
 * 
 * @author ziqing
 *
 */
public interface CollectiveSnapshotsEntry {

	/**
	 * The {@link ContractClauseKind} associates to this entry
	 * 
	 * @return
	 */
	ContractKind contractKind();

	/**
	 * If the entry is complete and can be dequeue for evaluation
	 * 
	 * @return
	 */
	boolean isComplete();

	/**
	 * If the process is recorded.
	 * 
	 * @param place
	 * @return
	 */
	boolean isRecorded(int place);

	/**
	 * Returns the number of {@link ImmutableMonoState} in this entry
	 * 
	 * @return
	 */
	int numMonoStates();

	/**
	 * Returns the identifier of this entry
	 * 
	 * @return
	 */
	int identifier();

	/**
	 * Returns the number of processes involved in this entry
	 * 
	 * @return
	 */
	int numInvolvedProcesses();

	/**
	 * Returns the message channels stored in this entry.
	 * 
	 *
	 * @return An array of length 2 of message buffers. one for "p2p" and the
	 *         other for "col"
	 */
	SymbolicExpression getMsgBuffers();

	/**
	 * Returns all stored assertion predicates (one for each process) in this
	 * entry.
	 * 
	 * @return
	 */
	Expression[] getAllAssertions();

	/**
	 * Insert a new {@link ImmutableMonoState} belonging to a DIFFERENT (if the
	 * process is existed, an error will be reported) process. Returns the
	 * number of the stored {@link ImmutableMonoState} after the insertion. If
	 * the insertion completes the entry, it changes the result which will be
	 * returned by {@link #isComplete()}.
	 * 
	 * @precondition The PID of the MonoState must be in
	 *               {@link #involvedProcesses()} and never be recorded i.e.
	 *               {@link #isRecorded(PID)} returns false and
	 *               {@link #isComplete()} returns false.
	 * @param monoState
	 * @return
	 */
	ImmutableCollectiveSnapshotsEntry insertMonoState(int place,
			ImmutableMonoState monoState, Expression assertion);

	Iterable<Pair<Variable, SymbolicExpression>> pickupJointVariables();

	ImmutableCollectiveSnapshotsEntry deliverJointVariables(
			List<Pair<Variable, SymbolicExpression>> vars);
}
