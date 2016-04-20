package edu.udel.cis.vsl.civl.state.persistent;

import java.io.PrintStream;
import java.util.Map;

import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.state.IF.DynamicScope;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.StackEntry;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

public class PersistentState extends PersistentObject implements State {

	/************************* Static Fields *************************/

	private final static int classCode = PersistentState.class.hashCode();

	/**
	 * The number of instances of this class that have been created since the
	 * class was loaded.
	 */
	private static long instanceCount = 0;

	/************************ Instance Fields ************************/

	/**
	 * If this is a canonic state (unique representative of its equivalence
	 * class), this field is the unique state ID for that class. Otherwise, it
	 * is -1.
	 */
	private int canonicId = -1;

	/**
	 * The absolutely unique ID number of this state, among all states ever
	 * created in this run of the JVM.
	 */
	private final long instanceId = instanceCount++;

	/**
	 * The process states. Entry at position i ontains the state of process of
	 * pid i. Some entries may be null.
	 */
	private ProcStateVector procVector;

	/**
	 * The dynamic scopes that exist in this state. The scope at position 0 is
	 * always the system scope.
	 */
	private DyscopeTree scopeTree;

	/**
	 * Non-null boolean-valued symbolic expression.
	 */
	private BooleanExpression pathCondition;

	/**
	 * Whether this state has been seen in the DFS search.
	 */
	private boolean seen = false;

	/**
	 * Whether this state is on the DFS search stack.
	 */
	private boolean onStack = false;

	/**
	 * Minimum depth at which this state has been encountered in DFS; used for
	 * finding minimal counterexample.
	 */
	private int depth = -1;

	/************************ Static Methods *************************/

	static long getInstanceCount() {
		return instanceCount;
	}

	static PersistentState newState(PersistentState state,
			ProcStateVector procVector, DyscopeTree scopeTree,
			BooleanExpression pathCondition) {
		PersistentState result = new PersistentState(
				procVector == null ? state.procVector : procVector,
				scopeTree == null ? state.scopeTree : scopeTree,
				pathCondition == null ? state.pathCondition : pathCondition);

		return result;
	}

	/************************** Constructors *************************/

	/**
	 * Constructs new instance with given fields. Nothing is cloned.
	 * 
	 * @param processStates
	 *            the process states; element at position i is state of process
	 *            of PID i; some entries may be null
	 * @param scopes
	 *            the dynamic scopes; element at position i is dyscope of
	 *            dyscope ID i; no null entries allowed
	 * @param pathCondition
	 *            non-null boolean valued symbolic expression
	 */
	PersistentState(ProcStateVector procVector, DyscopeTree scopeTree,
			BooleanExpression pathCondition) {
		this.procVector = procVector;
		this.scopeTree = scopeTree;
		this.pathCondition = pathCondition;
	}

	/******************** Package-private Methods ********************/

	/**
	 * Returns the instance ID of this State. The is obtained from a static
	 * counter that is incremented every time a state is instantiated.
	 * 
	 * @return this state's instance ID
	 */
	long getInstanceId() {
		return instanceId;
	}

	/**
	 * Returns the canonicID of this state. Returns -1 if it is not canonic.
	 * 
	 * @return canonicID of this state
	 */
	public int getCanonicId() {
		return canonicId;
	}

	void setCanonicId(int value) {
		canonicId = value;
	}

	PersistentDynamicScope getScope(int pid, Variable variable) {
		int scopeId = getProcessState(pid).getDyscopeId();
		Scope variableScope = variable.scope();
		PersistentDynamicScope scope;

		while (scopeId >= 0) {
			scope = getScope(scopeId);
			if (scope.lexicalScope() == variableScope)
				return scope;
			scopeId = getParentId(scopeId);
		}
		throw new IllegalArgumentException("Variable not in scope: " + variable);
	}

	int[] renumberScopes() {
		int numScopes = numScopes();

		if (numScopes == 0)
			return null; // no change
		else {
			int numProcs = numProcs();
			int[] oldToNew = new int[numScopes];
			int nextScopeId = 1;

			// the root dyscope is forced to be 0
			oldToNew[0] = 0;
			for (int i = 1; i < numScopes; i++)
				oldToNew[i] = -1;
			for (int pid = 0; pid < numProcs; pid++) {
				PersistentProcessState process = getProcessState(pid);

				if (process == null)
					continue;
				for (StackEntry entry : process.getStackEntries()) {
					int dynamicScopeId = entry.scope();

					while (oldToNew[dynamicScopeId] < 0) {
						oldToNew[dynamicScopeId] = nextScopeId;
						nextScopeId++;
						dynamicScopeId = getParentId(dynamicScopeId);
						if (dynamicScopeId < 0)
							break;
					}
				}
			}
			for (int i = 0; i < numScopes; i++) {
				if (oldToNew[i] != i)
					return oldToNew;
			}
			return null; // no change
		}
	}

	DyscopeTree getScopeTree() {
		return scopeTree;
	}

	ProcStateVector getProcStateVector() {
		return procVector;
	}

	PersistentState setScopeTree(DyscopeTree scopeTree) {
		return scopeTree == this.scopeTree ? this : new PersistentState(
				procVector, scopeTree, pathCondition);
	}

	PersistentState setProcVector(ProcStateVector procVector) {
		return procVector == this.procVector ? this : new PersistentState(
				procVector, scopeTree, pathCondition);
	}

	/**
	 * Adds a process state to this state.
	 * 
	 * The PID of the given state must be 1 greater than the current highest PID
	 * in this state, i.e., it must equal the length of the proc state vector,
	 * i.e., the current number of procs.
	 * 
	 * @param processState
	 *            a process state with PID numProcs
	 * @return new state same as old but with new process state added
	 */
	PersistentState addProcessState(PersistentProcessState processState) {
		return new PersistentState(new ProcStateVector(
				procVector.values.plus(processState)), scopeTree, pathCondition);
	}

	/**
	 * Removes a process state from this state. The process states with greater
	 * pid must be shifted down, their pids must be changed.
	 * 
	 * @param pid
	 *            PID in range [0,numProcs-1]
	 * @return new state same as old but the process state with given pid has
	 *         been removed, the subsequent processes shifted down and their
	 *         PIDs decremented, all process references in the state updated,
	 *         reachers updated in dyscopes?
	 */
	PersistentState removeProcessState(int pid, ModelFactory modelFactory) {
		ProcStateVector newProcVector = procVector.remove(pid);
		DyscopeTree newTree = scopeTree.shiftProcReferences(pid,
				newProcVector.size(), modelFactory);
		PersistentState result = new PersistentState(newProcVector, newTree,
				pathCondition);

		result = result.collectScopes(modelFactory);
		return result;
	}

	PersistentState collectScopes(ModelFactory modelFactory) {
		int[] oldToNew = renumberScopes();

		if (oldToNew == null) {
			return this;
		} else {
			PersistentState result = this;

			result = result.setScopeTree(scopeTree.renumberScopes(oldToNew,
					modelFactory));
			result = result.setProcVector(procVector.renumberScopes(oldToNew));
			return result;
		}
	}

	PersistentState setLocation(int pid, Location location) {
		PersistentProcessState procState = procVector.get(pid);
		CallStack callStack = procState.getCallStack();
		PersistentStackEntry entry = callStack.peek();

		if (location == entry.location())
			return this;
		else {
			callStack = callStack.replaceTop(entry.setLocation(location));
			procState = procState.setCallStack(callStack);

			return setProcVector((ProcStateVector) procVector.set(pid,
					procState));
		}
	}

	// PersistentState addScope(PersistentDynamicScope scope) {
	// DyscopeTree newTree = scopeTree.addScope(scope);
	//
	// return new PersistentState(procVector, newTree, pathCondition);
	// }

	/*********************** Methods from Object *********************/

	@Override
	public String toString() {
		return "State " + identifier();
	}

	/****************** Methods from PersistentObject ****************/

	@Override
	protected int computeHashCode() {
		return classCode ^ pathCondition.hashCode() ^ procVector.hashCode()
				^ scopeTree.hashCode();
	}

	@Override
	protected boolean computeEquals(PersistentObject obj) {
		if (obj instanceof PersistentState) {
			PersistentState that = (PersistentState) obj;

			return pathCondition.equals(that.pathCondition)
					&& procVector.equals(that.procVector)
					&& scopeTree.equals(that.scopeTree);
		}
		return false;
	}

	@Override
	protected void canonizeChildren(SymbolicUniverse universe,
			Map<PersistentObject, PersistentObject> canonicMap) {

		pathCondition = (BooleanExpression) universe.canonic(pathCondition);
		procVector = procVector.canonize(universe, canonicMap);
		scopeTree = scopeTree.canonize(universe, canonicMap);
		// this.canonicId = canonicId;
	}

	/*********************** Methods from State **********************/

	@Override
	public String identifier() {
		return canonicId + ":" + instanceId;
	}

	@Override
	public void commit() {
	}

	@Override
	public int numScopes() {
		return scopeTree.size();
	}

	@Override
	public int numProcs() {
		return procVector.size();
	}

	@Override
	public int rootScopeID() {
		return 0;
	}

	@Override
	public BooleanExpression getPathCondition() {
		return pathCondition;
	}

	@Override
	public boolean seen() {
		return seen;
	}

	@Override
	public boolean onStack() {
		return onStack;
	}

	@Override
	public void setSeen(boolean value) {
		this.seen = value;
	}

	@Override
	public void setOnStack(boolean onStack) {
		this.onStack = onStack;
	}

	@Override
	public int getParentId(int scopeId) {
		return getScope(scopeId).getParent();

	}

	@Override
	public int getScopeId(int pid, Variable variable) {
		int scopeId = getProcessState(pid).getDyscopeId();
		Scope variableScope = variable.scope();
		DynamicScope scope;

		while (scopeId >= 0) {
			scope = getScope(scopeId);
			if (scope.lexicalScope() == variableScope)
				return scopeId;
			scopeId = getParentId(scopeId);
		}
		throw new IllegalArgumentException("Variable not in scope: " + variable);
	}

	@Override
	public SymbolicExpression getVariableValue(int scopeId, int variableId) {
		DynamicScope scope = getScope(scopeId);

		return scope.getValue(variableId);
	}

	@Override
	public SymbolicExpression valueOf(int pid, Variable variable) {
		DynamicScope scope = getScope(pid, variable);
		int variableID = scope.lexicalScope().getVid(variable);

		return scope.getValue(variableID);
	}

	@Override
	public void print(PrintStream out) {
		out.println("State " + identifier());
		out.println("| Path condition");
		out.println("| | " + pathCondition);
		scopeTree.print(out, "| ");
		procVector.print(out, "| ");
		out.flush();
	}

	@Override
	public void setDepth(int value) {
		this.depth = value;
	}

	@Override
	public int getDepth() {
		return depth;
	}

	@Override
	public PersistentProcessState getProcessState(int pid) {
		return procVector.get(pid);
	}

	@Override
	public PersistentDynamicScope getScope(int id) {
		return scopeTree.get(id);
	}

	@Override
	public Iterable<? extends ProcessState> getProcessStates() {
		return procVector;
	}

	@Override
	public PersistentState setPathCondition(BooleanExpression pathCondition) {
		return pathCondition == this.pathCondition ? this
				: new PersistentState(procVector, scopeTree, pathCondition);
	}

	@Override
	public int numberOfReachers(int sid) {
		return scopeTree.get(sid).numberOfReachers();
	}

	@Override
	public boolean reachableByProcess(int sid, int pid) {
		return scopeTree.get(sid).reachableByProcess(pid);
	}

	@Override
	public PersistentState setVariable(int vid, int scopeId,
			SymbolicExpression value) {
		PersistentDynamicScope scope = scopeTree.get(scopeId);
		PersistentDynamicScope newScope = scope.setValue(vid, value);

		return scope == newScope ? this : new PersistentState(procVector,
				(DyscopeTree) scopeTree.set(scopeId, newScope), pathCondition);
	}

}
