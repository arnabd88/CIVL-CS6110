package edu.udel.cis.vsl.civl.state.IF;

import edu.udel.cis.vsl.civl.model.IF.expression.ContractClauseExpression.ContractKind;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.state.common.immutable.ImmutableCollectiveSnapshotsEntry;
import edu.udel.cis.vsl.civl.state.common.immutable.ImmutableMonoState;
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
	 * The {@link ContractKind} associates to this entry
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
	 * Returns the message channel specified by the source and destination.
	 * 
	 * @param src
	 *            The source of the messages in the channel
	 * @param dest
	 *            The destination of the messages in the channel
	 * @return
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
}
