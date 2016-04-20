package edu.udel.cis.vsl.civl.state.common.immutable;

import java.io.PrintStream;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Iterator;
import java.util.Map;

import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.state.IF.DynamicScope;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.StackEntry;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;

/**
 * A {@link ImmutableMonoState} is different from {@link ImmutableState} on that
 * it only contains one {@link ProcessState} and the corresponding
 * {@link DynamicScope} array to that ProcessState.
 * 
 * @author ziqing
 *
 */
public class ImmutableMonoState implements State {

	/**
	 * An {@link Iterator<?>} for {@link ProcessState}
	 * 
	 * @author ziqing
	 *
	 */
	class ProcessStateIterable implements Iterable<ProcessState> {
		class ProcessStateIterator implements Iterator<ProcessState> {
			int pos = 0;

			@Override
			public boolean hasNext() {
				return pos < 1;
			}

			@Override
			public ProcessState next() {
				if (0 == pos++) {
					return processState;
				} else {
					return null;
				}
			}

			@Override
			public void remove() {
				throw new UnsupportedOperationException();
			}

		}

		@Override
		public Iterator<ProcessState> iterator() {
			return new ProcessStateIterator();
		}
	}

	/* ************************ Static fields ************************ */
	/**
	 * The number of instances of this class that have been created since the
	 * class was loaded
	 */
	static long instanceCount = 0;

	/**
	 * ImmutableMonoState only contains at most one active process, calling some
	 * public interfaces requiring PID as an argument needs to provide the
	 * consistent PID. Otherwise, this message will be reported as an assertion
	 * failure information.
	 */
	static String inconsistentMsg = "Given PID is inconsistent with the PID of the single"
			+ " process state in a ImmutableMonoState";

	/* ************************ End of static fields ************************ */
	
	/* ************************ Instance fields ************************ */
	/**
	 * The path condition, a non-null boolean-valued symbolic expression
	 */
	private BooleanExpression pathCondition;
	/**
	 * The single process state wrapped by this class
	 */
	private ImmutableProcessState processState;
	/**
	 * An array of dynamic scopes referenced by the processState
	 */
	private ImmutableDynamicScope[] dyscopes;
	/**
	 * If this is a canonic state (unique representative of its equivalence
	 * class), this field is the unique state ID for that class. Otherwise, it
	 * is -1.
	 */
	private int canonicId = -1;
	/**
	 * Minimum depth at which this state has been encountered in DFS; used for
	 * finding minimal counterexample.
	 */
	private int depth = -1;
	/**
	 * Cached hashcode if it is computed
	 */
	private int hashCode = -1;
	/**
	 * Has the hashcode on this state already been computed ?
	 */
	private boolean hashed = false;
	/**
	 * Instance ID
	 */
	private final long instanceId = instanceCount++;
	/**
	 * Whether this state is on the DFS search stack
	 */
	private boolean onStack = false;
	/**
	 * Cached hashcode for the array of dynamic scopes
	 */
	private int scopeHashCode = -1;
	/**
	 * Whether the array of dynamic scopes is cached
	 */
	private boolean scopeHashed = false;
	/**
	 * Has this state been seen in the DFS search ?
	 */
	private boolean seen = false;

	/**
	 * Cached reference to the simplified version of this state
	 */
	ImmutableState simplifiedState = null;

	/* ****************** End of instance fields ****************** */
	
	/* ************************ Constructors ************************ */
	ImmutableMonoState(ImmutableProcessState processState,
			ImmutableDynamicScope[] dyscopes, BooleanExpression pathCondition) {
		assert processState != null;
		assert dyscopes != null;
		assert pathCondition != null;
		this.processState = processState;
		this.dyscopes = dyscopes;
		this.pathCondition = pathCondition;
	}

	/* ************************ Public methods ************************ */
	/**
	 * Return the single {@link ProcessState} inside this MonoState
	 * 
	 * @return
	 */
	public ImmutableProcessState getProcessState() {
		return processState;
	}

	/* ************************ Public interface methods ********************* */
	@Override
	public String identifier() {
		if (canonicId != -1)
			return String.valueOf(this.canonicId);
		else
			return canonicId + ":" + instanceId;
	}

	@Override
	public int numDyscopes() {
		return this.dyscopes.length;
	}

	@Override
	public int numProcs() {
		return 1;
	}

	@Override
	public int numLiveProcs() {
		int count;

		count = (null != processState) ? 1 : 0;
		return count;
	}

	@Override
	public int rootDyscopeID() {
		return 0;
	}

	@Override
	public BooleanExpression getPathCondition() {
		return this.pathCondition;
	}

	@Override
	public boolean seen() {
		return seen;
	}

	@Override
	public boolean onStack() {
		return this.onStack;
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
	public int getParentId(int dyscopeId) {
		return dyscopes[dyscopeId].getParent();
	}

	@Override
	public int getDyscopeID(int pid, Variable variable) {
		assert this.processState.getPid() == pid : ImmutableMonoState.inconsistentMsg;
		int dyscopeId = this.processState.getDyscopeId();
		Scope variableScope = variable.scope();
		DynamicScope dyscope;

		// searching all ancestor scopes because visible variables can only
		// come from ancestor scopes.
		while (dyscopeId >= 0) {
			dyscope = dyscopes[dyscopeId];
			if (dyscope.lexicalScope().equals(variableScope))
				return dyscopeId;
			dyscopeId = this.getParentId(dyscopeId);
		}
		return -1;
	}

	@Override
	public SymbolicExpression getVariableValue(int dyscopeID, int variableID) {
		return dyscopes[dyscopeID].getValue(variableID);
	}

	@Override
	public SymbolicExpression valueOf(int pid, Variable variable) {
		assert this.processState.getPid() == pid : ImmutableMonoState.inconsistentMsg;
		return this.getVariableValue(pid, variable.vid());
	}

	@Override
	public StringBuffer callStackToString() {
		StringBuffer result = new StringBuffer();

		result.append("\nCall stacks:\n");
		result.append("\n");
		result.append(this.processState.toSBrieftringBuffer());
		return result;
	}

	@Override
	public void setDepth(int value) {
		this.depth = value;
	}

	@Override
	public int getDepth() {
		return this.depth;
	}

	@Override
	public ProcessState getProcessState(int pid) {
		assert this.processState.getPid() == pid : ImmutableMonoState.inconsistentMsg;
		return this.processState;
	}

	@Override
	public ImmutableDynamicScope getDyscope(int id) {
		return this.dyscopes[id];
	}

	@Override
	public int getDyscope(int pid, Scope scope) {
		assert this.processState.getPid() == pid : ImmutableMonoState.inconsistentMsg;
		this.getDyscope(pid, scope.id());
		return 0;
	}

	@Override
	public int getDyscope(int pid, int scopeID) {
		Iterator<StackEntry> stackIter = processState.getStackEntries()
				.iterator();
		int currentDyscopeID = -1;
		DynamicScope currentDyscope;

		// First, searching the call stack for the matching static scope
		while (stackIter.hasNext()) {
			StackEntry currentEntry = stackIter.next();

			currentDyscopeID = currentEntry.scope();
			currentDyscope = dyscopes[currentDyscopeID];
			if (scopeID == currentDyscope.lexicalScope().id())
				return currentEntry.scope();
		}
		// Second, if there is no matching static scope in call stack,
		// searching starts from the bottom scope of the call stack on all of
		// its ancestors.
		currentDyscopeID = this.getParentId(currentDyscopeID);
		while (0 <= currentDyscopeID) {
			currentDyscope = dyscopes[currentDyscopeID];
			if (scopeID == currentDyscope.lexicalScope().id())
				return currentDyscopeID;
			currentDyscopeID = this.getParentId(currentDyscopeID);
		}
		return -1;
	}

	@Override
	public Iterable<? extends ProcessState> getProcessStates() {
		return new ProcessStateIterable();
	}

	@Override
	public ImmutableMonoState setPathCondition(BooleanExpression pathCondition) {
		ImmutableMonoState result = new ImmutableMonoState(processState,
				dyscopes, pathCondition);

		if (scopeHashed) {
			result.scopeHashed = true;
			result.scopeHashCode = scopeHashCode;
		}
		return result;
	}

	@Override
	public int numberOfReachers(int sid) {
		return dyscopes[sid].numberOfReachers();
	}

	@Override
	public boolean reachableByProcess(int sid, int pid) {
		return dyscopes[sid].reachableByProcess(pid);
	}

	@Override
	public int getCanonicId() {
		return canonicId;
	}

	@Override
	public void print(PrintStream out) {
		int numScopes = numDyscopes();

		out.print("MonoState " + identifier());
		out.println();
		out.println("| Path condition");
		out.println("| | " + pathCondition);
		out.println("| Dynamic scopes");
		for (int i = 0; i < numScopes; i++) {
			ImmutableDynamicScope dyscope = (ImmutableDynamicScope) dyscopes[i];

			if (dyscope == null)
				out.println("| | dyscope - (id=" + i + "): null");
			else
				this.printImmutableDynamicScope(out, dyscope, "" + i, "| | ");
		}
		out.println("| Process states");

		if (processState == null)
			out.println("| | process - (id=" + processState.getPid()
					+ "): null");
		else
			processState.print(out, "| | ");
		out.flush();
	}

	/* **************** Private methods ***************** */
	/**
	 * Implements the flyweight pattern for ImmutableDynamicScopes: if there
	 * already exists a dyscope which is equivalent to the given dyscope, return
	 * that one, otherwise, add the dyscope to the table and return it.
	 * 
	 * This method goes into the dyscope and replaces each individual symbolic
	 * expression with the canonic version of that symbolic expression.
	 * 
	 * @param dyscope
	 *            the dyscope to be flyweighted
	 * @param scopeMap
	 *            the map to use for flyweighting in which the key-value pairs
	 *            have the form (X,X) for all canonic objects X
	 * @return the unique representative of the dyscope's equivalence class
	 */
	private ImmutableDynamicScope canonic(ImmutableDynamicScope dyscope,
			Map<ImmutableDynamicScope, ImmutableDynamicScope> scopeMap,
			SymbolicUniverse universe) {
		ImmutableDynamicScope canonicScope = scopeMap.get(dyscope);

		if (canonicScope == null) {
			dyscope.makeCanonic(universe);
			scopeMap.put(dyscope, dyscope);
			return dyscope;
		}
		return canonicScope;
	}

	/**
	 * Implements the flyweight pattern for ImmutableProcessState: if there
	 * already exists a process state which is equivalent to the given one,
	 * return that one, otherwise, add the process state to the table and return
	 * it.
	 * 
	 * @param processState
	 *            the process state to be flyweighted
	 * @param scopeMap
	 *            the map to use for flyweighting in which the key-value pairs
	 *            have the form (X,X) for all canonic objects X
	 * @return the unique representative of the process state's equivalence
	 *         class
	 */
	private ImmutableProcessState canonic(ImmutableProcessState processState,
			Map<ImmutableProcessState, ImmutableProcessState> processMap) {
		ImmutableProcessState canonicProcessState = processMap
				.get(processState);

		if (canonicProcessState == null) {
			processState.makeCanonic();
			processMap.put(processState, processState);
			return processState;
		}
		return canonicProcessState;
	}

	/**
	 * Prints a dyscope of a given id of this state to the given print stream.
	 * 
	 * @param out
	 *            The print stream to be used.
	 * @param dyscope
	 *            The dyscope to be printed.
	 * @param id
	 *            The id of the dyscope to be printed.
	 * @param prefix
	 *            The line prefix of the printing result.
	 */
	private void printImmutableDynamicScope(PrintStream out,
			ImmutableDynamicScope dyscope, String id, String prefix) {
		Scope lexicalScope = dyscope.lexicalScope();
		int numVars = lexicalScope.numVariables();
		BitSet reachers = dyscope.getReachers();
		int bitSetLength = reachers.length();
		boolean first = true;

		out.println(prefix + "dyscope " + dyscope.name() + " (id=" + id
				+ ", parent ID=" + dyscope.getParent() + ", static="
				+ lexicalScope.id() + ")");
		out.print(prefix + "| reachers = {");
		for (int j = 0; j < bitSetLength; j++) {
			if (reachers.get(j)) {
				if (first)
					first = false;
				else
					out.print(",");
				out.print(j);
			}
		}
		out.println("}");
		out.println(prefix + "| variables");
		for (int i = 0; i < numVars; i++) {
			Variable variable = lexicalScope.variable(i);
			SymbolicExpression value = dyscope.getValue(i);

			out.print(prefix + "| | " + variable.name() + " = ");
			if (variable.type().isPointerType()) {
				out.println(this.pointerValueToString(value));
			} else
				out.println(value);
		}
		out.flush();
	}

	/**
	 * Obtains the string representation of a pointer value.
	 * 
	 * @param pointer
	 *            The pointer value whose string representation is to be
	 *            generated.
	 * @return The string representation of the given pointer value.s
	 */
	private String pointerValueToString(SymbolicExpression pointer) {
		StringBuffer result = new StringBuffer();

		if (pointer.operator() == SymbolicOperator.NULL)
			return pointer.toString();
		else {
			result.append('&');
			return result.toString();
		}
	}

	/* **************** Package private methods ***************** */
	/**
	 * Makes this state canonic. Recursively makes the path condition, dynamic
	 * scopes, and process states canonic, then applies the flyweight pattern to
	 * this state.
	 * 
	 * @param canonicId
	 *            the canonic ID to assign to this state
	 * @param universe
	 *            the symbolic universe used to canonize symbolic expressions
	 * @param scopeMap
	 *            the map used to flyweight dynamic scopes
	 * @param processMap
	 *            the map used to flyweight process states
	 */
	void makeCanonic(int canonicId, SymbolicUniverse universe,
			Map<ImmutableDynamicScope, ImmutableDynamicScope> scopeMap,
			Map<ImmutableProcessState, ImmutableProcessState> processMap) {
		int numScopes = dyscopes.length;

		pathCondition = (BooleanExpression) universe.canonic(pathCondition);
		processState = canonic(processState, processMap);
		for (int i = 0; i < numScopes; i++) {
			ImmutableDynamicScope scope = dyscopes[i];

			if (!scope.isCanonic())
				dyscopes[i] = canonic(scope, scopeMap, universe);
		}
		this.canonicId = canonicId;
	}

	/**
	 * Set the {@link DynamicScope} set for a {@link ImmutableMonoState},
	 * returns a new {@link ImmutableMonoState}
	 * 
	 * @param dyscopes
	 *            The new array of {@link DynamicScope}s
	 * @return a new {@link ImmutableMonoState}
	 */
	ImmutableMonoState setDyscopes(ImmutableDynamicScope[] dyscopes) {
		ImmutableMonoState newState = new ImmutableMonoState(processState,
				dyscopes, pathCondition);

		newState.depth = this.depth;
		return newState;

	}

	/* **************** Object override methods ***************** */
	@Override
	public boolean equals(Object obj) {
		ImmutableMonoState other;

		if (this == obj)
			return true;
		if (!(obj instanceof ImmutableMonoState))
			return false;
		other = (ImmutableMonoState) obj;
		if (canonicId >= 0 && other.canonicId >= 0)
			return canonicId == other.canonicId;
		if (hashed && other.hashed && hashCode != other.hashCode)
			return false;
		if (!pathCondition.equals(other.pathCondition))
			return false;
		if (scopeHashed && other.scopeHashed
				&& scopeHashCode != other.scopeHashCode)
			return false;
		if (!processState.equals(other.processState))
			return false;
		if (!Arrays.equals(dyscopes, other.dyscopes))
			return false;
		return true;
	}

	@Override
	public String toString() {
		return "MonoState " + identifier();
	}

	@Override
	public int hashCode() {
		if (!hashed) {
			if (!scopeHashed) {
				scopeHashCode = Arrays.hashCode(dyscopes);
				scopeHashed = true;
			}
			hashCode = pathCondition.hashCode() ^ scopeHashCode
					^ this.processState.getPid();
			hashed = true;
		}
		return hashCode;
	}

	@Override
	public SymbolicExpression[] getOutputValues(String[] outputNames) {
		// Note: current monoStates can only be used as snapshots for MPI
		// contracts, there is no shared output variables in this circumstances.
		return new SymbolicExpression[0];
	}

	@Override
	public boolean isFinalState() {
		return processState.hasEmptyStack();
	}
}
