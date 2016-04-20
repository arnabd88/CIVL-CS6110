package edu.udel.cis.vsl.civl.state.common.immutable;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import edu.udel.cis.vsl.civl.model.IF.contract.FunctionContract.ContractKind;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.state.IF.CollectiveSnapshotsEntry;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.util.IF.Pair;
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

	/**
	 * A pick up station is a {@link List} of <vid, value> pairs. For some cases
	 * that all processes have the same properties, the first process deliveries
	 * the values of all of these variables.
	 */
	private List<Pair<Variable, SymbolicExpression>> pickUpStation;

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
		this.pickUpStation = null;
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
		this.pickUpStation = null;
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
		clone.pickUpStation = copyJointVariables();
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
		newEntry.pickUpStation = copyJointVariables();
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
		if (pickUpStation != null) {
			for (Pair<Variable, SymbolicExpression> jointVal : pickUpStation) {
				jointVal.right = universe.canonic(jointVal.right);
			}
		}
	}

	ImmutableCollectiveSnapshotsEntry simplify(State state) {
		ImmutableMonoState[] newMonoStates;
		ImmutableCollectiveSnapshotsEntry newCollectiveEntry;
		BooleanExpression newPathCondition;
		Reasoner reasoner = universe.reasoner(state.getPathCondition());

		newMonoStates = this.monoStates.clone();
		for (int place = 0; place < this.numProcesses; place++) {
			if (isRecorded[place]) {
				ImmutableMonoState monoState = monoStates[place];
				ImmutableDynamicScope[] newScopes;
				int numDyscopes = monoState.numDyscopes();

				newScopes = new ImmutableDynamicScope[numDyscopes];
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
				newPathCondition = reasoner.simplify(state.getPathCondition());
				if (newPathCondition != monoState.getPathCondition()) {
					newMonoStates[place] = newMonoStates[place]
							.setPathCondition(newPathCondition);
				}
				this.isSimplified[place] = true;
			}
		}
		newCollectiveEntry = copy();
		// Simplify pick up station:
		if (newCollectiveEntry.pickUpStation != null)
			for (Pair<Variable, SymbolicExpression> pickup : newCollectiveEntry.pickUpStation)
				pickup.right = reasoner.simplify(pickup.right);
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
		return "Snapshot entry: " + identifier;
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

	@Override
	public Iterable<Pair<Variable, SymbolicExpression>> pickupJointVariables() {
		return this.copyJointVariables();
	}

	@Override
	public ImmutableCollectiveSnapshotsEntry deliverJointVariables(
			List<Pair<Variable, SymbolicExpression>> vars) {
		ImmutableCollectiveSnapshotsEntry clone = copy();

		if (vars != null) {
			clone.pickUpStation = new LinkedList<>();
			for (Pair<Variable, SymbolicExpression> item : vars) {
				clone.pickUpStation.add(new Pair<>(item.left, universe
						.canonic(item.right)));
			}
		}
		return clone;
	}

	// TODO:optimize this:
	private List<Pair<Variable, SymbolicExpression>> copyJointVariables() {
		List<Pair<Variable, SymbolicExpression>> clone = new LinkedList<>();

		if (pickUpStation == null)
			return new LinkedList<>();
		for (Pair<Variable, SymbolicExpression> item : pickUpStation) {
			clone.add(new Pair<>(item.left, universe.canonic(item.right)));
		}
		return clone;
	}
}
