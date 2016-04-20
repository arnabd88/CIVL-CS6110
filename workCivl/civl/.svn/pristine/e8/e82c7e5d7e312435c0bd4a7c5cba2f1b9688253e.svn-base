package edu.udel.cis.vsl.civl.state.common.immutable;

import java.util.Map;

import edu.udel.cis.vsl.civl.model.IF.contract.FunctionContract.ContractKind;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.state.IF.CollectiveSnapshotsEntry;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

public class ImmutableCollectiveSnapshotsEntry implements
		CollectiveSnapshotsEntry {
	/**
	 * Static instance identifier
	 */
	private static int instanceId = 0;
	/**
	 * The array stores {@link ImmutableMonoState}
	 */
	private ImmutableMonoState[] monoStates;

	/**
	 * The number of inserted {@link ImmutableMonoState}
	 */
	private int numMonoStates;
	/**
	 * The array stores assertion predicates for each process
	 */
	private Expression[] predicates;

	/**
	 * Indicating if the entry is complete and can be dequeue.
	 */
	private boolean isComplete;

	/**
	 * Indicating if this entry has been simplified.
	 */
	private boolean[] isSimplified;

	private boolean[] isRecorded;

	/**
	 * Identifier of this entry
	 */
	private final int identifier = ++instanceId;

	/**
	 * The total number of processes involved in the corresponding
	 * {@link ImmutableState};
	 */
	private int numProcesses;

	private int maxPid;

	/**
	 * The {@link ContractKind} of this entry
	 */
	private ContractKind kind;

	/**
	 * Communicator channels, coordinated by source then destination.
	 */
	private SymbolicExpression channels;

	private SymbolicUniverse universe;

	/* *********************** Constructor ************************* */
	/**
	 * Create a {@link ImmutableCollectiveSnapshotsEnrty} which stores snapshots
	 * for one collective assertion. One
	 * {@link ImmutableCollectiveSnapshotsEnrty} should be correspond to one
	 * {@link ImmutableState}.
	 * 
	 * @param involvedProcesses
	 *            The PIDs of processes involved in the collective assertion,
	 *            such a information are always provided by an argument of the
	 *            collective assertion such as a MPI communicator.
	 * @param processesInState
	 *            Total number of processes in the corresponding state
	 * @param identifier
	 * @param channels
	 *            The messages channels in communicator
	 */
	ImmutableCollectiveSnapshotsEntry(int numProcesses,
			SymbolicUniverse universe) {
		this.numProcesses = numProcesses;
		this.isComplete = false;
		this.numMonoStates = 0;
		this.monoStates = new ImmutableMonoState[numProcesses];
		this.predicates = new Expression[numProcesses];
		this.isSimplified = new boolean[numProcesses];
		this.isRecorded = new boolean[numProcesses];
		for (int i = 0; i < numProcesses; i++) {
			this.isSimplified[i] = false;
			this.isRecorded[i] = false;
		}
		this.universe = universe;
		this.maxPid = 0;
		this.kind = null;
	}

	ImmutableCollectiveSnapshotsEntry(int numProcesses,
			SymbolicUniverse universe, ContractKind kind) {
		this.numProcesses = numProcesses;
		this.isComplete = false;
		this.numMonoStates = 0;
		this.monoStates = new ImmutableMonoState[numProcesses];
		this.predicates = new Expression[numProcesses];
		this.isSimplified = new boolean[numProcesses];
		this.isRecorded = new boolean[numProcesses];
		for (int i = 0; i < numProcesses; i++) {
			this.isSimplified[i] = false;
			this.isRecorded[i] = false;
		}
		this.universe = universe;
		this.maxPid = 0;
		this.kind = kind;
	}

	public ImmutableCollectiveSnapshotsEntry copy() {
		ImmutableCollectiveSnapshotsEntry clone = new ImmutableCollectiveSnapshotsEntry(
				this.numProcesses, universe);
		clone.isComplete = isComplete;
		clone.numMonoStates = numMonoStates;
		clone.monoStates = monoStates.clone();
		clone.predicates = predicates.clone();
		clone.isSimplified = isSimplified.clone();
		clone.isRecorded = this.isRecorded.clone();
		clone.maxPid = this.maxPid;
		clone.channels = channels;
		clone.kind = this.kind;
		return clone;
	}

	/* *********************** Public Methods ************************* */
	@Override
	public boolean isComplete() {
		return isComplete;
	}

	@Override
	public int numMonoStates() {
		return numMonoStates;
	}

	@Override
	public int identifier() {
		return identifier;
	}

	@Override
	public int numInvolvedProcesses() {
		return this.numProcesses;
	}

	@Override
	public Expression[] getAllAssertions() {
		return predicates;
	}

	@Override
	public SymbolicExpression getMsgBuffers() {
		return channels;
	}

	@Override
	public boolean isRecorded(int place) {
		return this.isRecorded[place];
	}

	@Override
	public ImmutableCollectiveSnapshotsEntry insertMonoState(int place,
			ImmutableMonoState monoState, Expression assertion) {
		ImmutableCollectiveSnapshotsEntry newEntry;
		int pid = monoState.getProcessState().getPid();

		assert !isComplete;
		newEntry = this.copy();
		newEntry.monoStates[place] = monoState;
		newEntry.predicates[place] = assertion;
		newEntry.numMonoStates++;
		newEntry.isRecorded[place] = true;
		newEntry.kind = kind;
		if (pid >= newEntry.maxPid)
			newEntry.maxPid = pid;
		// If all snapshots are taken, check if they are coming from the correct
		// processes set.
		if (newEntry.numMonoStates == newEntry.numProcesses)
			newEntry.isComplete = true;
		return newEntry;
	}

	// TODO: why max pid ?
	public int getMaxPid() {
		return this.maxPid;
	}

	/* ************* Simplification and collection interfaces **************** */
	void makeCanonic(int canonicId,
			Map<ImmutableDynamicScope, ImmutableDynamicScope> scopeMap,
			Map<ImmutableProcessState, ImmutableProcessState> processesMap) {
		if (monoStates == null)
			return;
		for (ImmutableMonoState state : monoStates)
			if (state != null)
				state.makeCanonic(canonicId, universe, scopeMap, processesMap);
		channels = (channels != null) ? universe.canonic(channels) : null;
	}

	CollectiveSnapshotsEntry simplify() {
		ImmutableMonoState[] newMonoStates;
		ImmutableCollectiveSnapshotsEntry newCollectiveEntry;
		BooleanExpression newPathCondition;

		newMonoStates = this.monoStates.clone();
		for (int place = 0; place < this.numProcesses; place++) {
			if (isRecorded[place]) {
				Reasoner reasoner;
				ImmutableMonoState monoState = monoStates[place];
				ImmutableDynamicScope[] newScopes;
				int numDyscopes = monoState.numDyscopes();

				newScopes = new ImmutableDynamicScope[numDyscopes];
				reasoner = universe.reasoner(monoState.getPathCondition());
				for (int sid = 0; sid < numDyscopes; sid++) {
					ImmutableDynamicScope oldDyscope = monoState
							.getDyscope(sid);
					ImmutableDynamicScope newDyscope;
					int numVars = oldDyscope.numberOfVariables();
					SymbolicExpression[] newVarValues = new SymbolicExpression[numVars];

					for (int vid = 0; vid < numVars; vid++) {
						SymbolicExpression oldValue = oldDyscope.getValue(vid);
						SymbolicExpression newValue = reasoner
								.simplify(oldValue);

						newVarValues[vid] = newValue;
					}
					newDyscope = oldDyscope.setVariableValues(newVarValues);
					newScopes[sid] = newDyscope;
				}
				newMonoStates[place] = monoState.setDyscopes(newScopes);
				newPathCondition = reasoner.getReducedContext();
				if (newPathCondition != monoState.getPathCondition()) {
					newMonoStates[place] = newMonoStates[place]
							.setPathCondition(newPathCondition);
				}
				this.isSimplified[place] = true;
			}
		}
		newCollectiveEntry = copy();
		newCollectiveEntry.monoStates = newMonoStates;
		return newCollectiveEntry;
	}

	ImmutableMonoState[] getMonoStates() {
		return this.monoStates;
	}

	@Override
	public ContractKind contractKind() {
		return kind;
	}

	@Override
	public String toString() {
		return "Snapshot entry: " + instanceId;
	}

	ImmutableCollectiveSnapshotsEntry setMsgBuffers(SymbolicExpression channels) {
		ImmutableCollectiveSnapshotsEntry newEntry = this.copy();

		newEntry.channels = (channels != null) ? universe.canonic(channels)
				: null;
		return newEntry;
	}

	ImmutableCollectiveSnapshotsEntry setKind(ContractKind kind) {
		ImmutableCollectiveSnapshotsEntry newEntry = this.copy();

		newEntry.kind = kind;
		return newEntry;
	}
}
