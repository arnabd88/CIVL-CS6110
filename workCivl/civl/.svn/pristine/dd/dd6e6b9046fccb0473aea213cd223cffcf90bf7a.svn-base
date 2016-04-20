package edu.udel.cis.vsl.civl.state.trans;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.state.IF.DynamicScope;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.StackEntry;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.util.Pair;
import edu.udel.cis.vsl.civl.util.Transmuter;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

public class TransientState extends TransientObject implements State {

	/**
	 * A node in the dynamic scope tree.
	 * 
	 * @author siegel
	 * 
	 */
	class DyscopeNode {

		DyscopeNode(int id, DynamicScope scope, DyscopeNode parent,
				BitSet reachers) {
			this.id = id;
			this.scope = scope;
			this.parent = parent;
			this.reachers = reachers;
		}

		/**
		 * The dynamic scope ID. This is also the index of this node in the
		 * array dyscopeNodes. Extrinsic data, since it is already determined by
		 * the position of this node in the array dyscopeNodes.
		 */
		int id;

		/**
		 * The dynamic scope itself, which specifies a static scope, and a value
		 * for every variable in the static scope. Intrinsic data.
		 */
		DynamicScope scope;

		/**
		 * The dyscope node of the parent of this node, or null if this is the
		 * root node. Intrinsic data.
		 */
		DyscopeNode parent;

		/**
		 * The set of processes which can reach this node by following edges
		 * from their call stacks and the parent edges in the dyscope tree.
		 * Extrinsic data, as it is already determined by the process states and
		 * dynamic scopes.
		 */
		BitSet reachers;

		@Override
		public int hashCode() {
			// 2097593 is a prime number I found on Wikipedia
			if (parent == null)
				return scope.hashCode() ^ 2097593;
			return scope.hashCode() ^ (2097593 * (2 + parent.id));
		}

		@Override
		public boolean equals(Object object) {
			if (object instanceof DyscopeNode) {
				DyscopeNode that = (DyscopeNode) object;

				if (!scope.equals(that.scope))
					return false;
				if (parent == null)
					return that.parent == null;
				if (that.parent == null)
					return false;
				return parent.id == that.parent.id;
			}
			return false;
		}

		@Override
		public String toString() {
			return "DyscopeNode " + id;
		}

		public void print(PrintStream out, String prefix) {
			out.println(prefix + "Dyscope node " + id);
			out.println(prefix + "| parent = "
					+ (parent == null ? "null" : parent.id));
			out.print(prefix + "| reachers = {");
			{
				boolean first = true;

				for (int i = reachers.nextSetBit(0); i >= 0; i = reachers
						.nextSetBit(i + 1)) {
					if (first)
						first = false;
					else
						out.print(",");
					out.print(i);
				}
			}
			out.println("}");
			scope.print(out, prefix + "| ");
			out.flush();
		}
	}

	// Static fields...

	/**
	 * The number of instances of this class that have been created since the
	 * class was loaded.
	 */
	static long instanceCount = 0;

	// Instance fields (intrinsic)...

	/**
	 * Non-null boolean-valued symbolic expression. Intrinsic data.
	 */
	private BooleanExpression pathCondition;

	/**
	 * The state of each process in this state. The process at index i has PID
	 * i. Some entires may be null. Intrinsic data.
	 */
	private ArrayList<ProcessState> processStates;

	/**
	 * The dynamic scopes that exist in this state. The scope at index 0 is
	 * always the system scope. The scope at index i has dyscope ID i. Some
	 * entries may be null. Intrinsic data.
	 */
	private ArrayList<DyscopeNode> scopeNodes;

	// Instance fields (extrinsic)...

	/**
	 * Whether this state has been seen in the DFS search. This is extrinsic
	 * data.
	 */
	private boolean seen = false;

	/**
	 * Whether this state is on the DFS search stack. Extrinsic data.
	 */
	private boolean onStack = false;

	/**
	 * Minimum depth at which this state has been encountered in DFS; used for
	 * finding minimal counterexample. Extrinsic data.
	 */
	private int depth = -1;

	// Constructors...

	/**
	 * Basic constructor. The arrays are used as fields---the elements are not
	 * copied into a new array. All arguments must be non-null. Seen and onStack
	 * bits are set to false.
	 * 
	 * @param processes
	 * @param scopes
	 * @param buffers
	 * @param pathCondition
	 */
	TransientState(ArrayList<ProcessState> processes,
			ArrayList<DyscopeNode> scopeNodes, BooleanExpression pathCondition) {
		super(instanceCount++);
		assert processes != null;
		assert scopeNodes != null;
		assert pathCondition != null;
		this.processStates = processes;
		this.scopeNodes = scopeNodes;
		this.pathCondition = pathCondition;
	}

	// Private methods...

	/**
	 * Returns a new array list of new dynamic scope nodes obtained by copying
	 * the existing ones. This is a semi-deep copy: a new list is created, and
	 * each node in the list is new, but the fields of the node may be shared
	 * with the fields of the original nodes. The parent fields are configured
	 * correctly to point to the new nodes, not the original nodes.
	 * 
	 * @param initialCapacity
	 *            the initial capacity used to instantiate the new array list.
	 * 
	 * @return semi-deep copy of scopeNodes
	 */
	private ArrayList<DyscopeNode> cloneNodes(int initialCapacity) {
		int n = scopeNodes.size();
		ArrayList<DyscopeNode> newNodes = new ArrayList<DyscopeNode>(
				initialCapacity);

		for (DyscopeNode node : scopeNodes) {
			DyscopeNode newNode = new DyscopeNode(node.id, node.scope, null,
					(BitSet) node.reachers.clone());

			newNodes.add(newNode);
		}
		for (int i = 0; i < n; i++) {
			DyscopeNode oldNode = scopeNodes.get(i);
			DyscopeNode newNode = newNodes.get(i);
			DyscopeNode oldParent = oldNode.parent;

			if (oldParent != null)
				newNode.parent = newNodes.get(oldParent.id);
		}
		return newNodes;
	}

	/**
	 * Returns a new array list of new dynamic scope nodes obtained by copying
	 * the existing ones. This is a semi-deep copy: a new list is created, and
	 * each node in the list is new, but the fields of the node may be shared
	 * with the fields of the original nodes. The parent fields are configured
	 * correctly to point to the new nodes, not the original nodes.
	 * 
	 * The initial capacity used to the new array list is the number of nodes.
	 * If you plan on adding more nodes to this list, you might want to specify
	 * a larger initial capacity using method {@link #cloneNodes(int)}.
	 * 
	 * @return semi-deep copy of scopeNodes
	 */
	private ArrayList<DyscopeNode> cloneNodes() {
		return cloneNodes(scopeNodes.size());
	}

	@SuppressWarnings("unchecked")
	private ArrayList<ProcessState> cloneProcStates() {
		return (ArrayList<ProcessState>) processStates.clone();
	}

	/**
	 * Determines the set of reachable dynamic scopes in this state and numbers
	 * them in a canonical way. Scopes are numbered from 0 up, in the order in
	 * which they are encountered by iterating over the processes by increasing
	 * ID, iterating over the process' call stack frames from the bottom up,
	 * iterating over the parent scopes from the scope referenced by the frame.
	 * The one exception to this pattern is that the root scope is always
	 * assigned ID 0, assuming it is reachable.
	 * 
	 * Unreachable scopes are assigned the number -1.
	 * 
	 * Returns a pair. Left component is an array of length numScopes in which
	 * the element at position i is the new ID number for the scope whose old ID
	 * number is i. If a scope is not reachable, its entry will be -1. The right
	 * component is the number of reachable scopes, i.e., the number of
	 * nonnegative entries in the map.
	 * 
	 * Does not modify anything.
	 * 
	 * @return pair in which left component is the old-to-new ID map, and the
	 *         right component is the number of reachable scopes
	 */
	private Pair<int[], Integer> numberScopes() {
		int numScopes = numScopes();
		int[] oldToNew = new int[numScopes];
		int numReachable;

		if (numScopes == 0)
			numReachable = 0;
		else {
			boolean allStacksEmpty = true;

			// assume the root scope is reachable and
			// force it to have dyscope ID 0:
			numReachable = 1;
			oldToNew[0] = 0;
			for (int i = 1; i < numScopes; i++)
				oldToNew[i] = -1;
			for (ProcessState processState : processStates) {
				if (processState != null) {
					Iterator<? extends StackEntry> iter = processState
							.bottomToTopIterator();

					while (iter.hasNext()) {
						int dynamicScopeId = iter.next().scope();

						allStacksEmpty = false;
						while (oldToNew[dynamicScopeId] < 0) {
							oldToNew[dynamicScopeId] = numReachable;
							numReachable++;
							dynamicScopeId = getParentId(dynamicScopeId);
							if (dynamicScopeId < 0)
								break;
						}
					}
				}
			}
			if (allStacksEmpty) {
				// since all stacks are empty, the root scope
				// was not reached, so undo what you did above:
				oldToNew[0] = -1;
				numReachable = 0;
			}
		}
		return new Pair<int[], Integer>(oldToNew, numReachable);
	}

	/**
	 * Given the map from old dynamic scope IDs to new dynamic scope IDs, this
	 * method returns the map on symbolic expressions which maps a scope value
	 * to the new value. The scope values are symbolic expressions which
	 * essentially wrap a concrete integer, the dynamic scope ID. If the state
	 * contains such references, they must be updated to reflect the new
	 * numbering. This map can be used to assist with that.
	 * 
	 * For scopes which are unreachable (map to -1 in the oldToNewSidMap), the
	 * new scope value will be a special "undefined" value.
	 * 
	 * Nothing is modified by this method.
	 * 
	 * @param oldToNewSidMap
	 *            map from old scope ID to new; array of length number of
	 *            dynamic scopes; -1 is used to indicate an unreachable scope
	 *            which will be removed
	 * @param modelFactory
	 *            the model factory used to produce scope values
	 * @return a map from old scope values to new
	 */
	private Map<SymbolicExpression, SymbolicExpression> scopeSubMap(
			int[] oldToNewSidMap, ModelFactory modelFactory) {
		int size = oldToNewSidMap.length;
		Map<SymbolicExpression, SymbolicExpression> result = new HashMap<SymbolicExpression, SymbolicExpression>(
				size);

		for (int i = 0; i < size; i++) {
			int newId = oldToNewSidMap[i];

			if (newId != i) {
				SymbolicExpression oldVal = modelFactory.scopeValue(i);
				SymbolicExpression newVal = modelFactory
						.scopeValue(oldToNewSidMap[i]);

				result.put(oldVal, newVal);
			}
		}
		return result;
	}

	/**
	 * Updates the scope values occurring in a dynamic scope. The old values are
	 * replaced with new ones according to the scopeSubMap. Either the given
	 * dynamic scope is modified, or a new one is created and returned,
	 * depending on whether the dynamic scope is mutable.
	 * 
	 * @param scopeSubMap
	 *            mapping of old scope values to new ones
	 * @param universe
	 *            the symbolic universe that will be used to perform the
	 *            substitution
	 * @param scope
	 *            the dynamic scope which contains variable values that will be
	 *            modified by substitution
	 * @return either a new dynamic scope or the modified original one
	 */
	private DynamicScope updateScopeReferences(
			Map<SymbolicExpression, SymbolicExpression> scopeSubMap,
			SymbolicUniverse universe, DynamicScope scope) {
		Scope staticScope = scope.lexicalScope();
		Collection<Variable> scopeVariableIter = staticScope
				.variablesWithScoperefs();

		for (Variable variable : scopeVariableIter) {
			int vid = variable.vid();
			SymbolicExpression oldValue = scope.getValue(vid);

			assert oldValue != null;
			if (!oldValue.isNull()) {
				SymbolicExpression newValue = universe.substitute(oldValue,
						scopeSubMap);

				if (oldValue != newValue)
					scope = scope.setValue(vid, newValue);
			}
		}
		return scope;
	}

	/**
	 * Updates the scope values occurring in a state. The update is specified by
	 * the oldToNewSidMap, which maps old dynamic scope IDs to new ones. This
	 * method iterates over all dynamic scopes occurring in the state, and over
	 * all variable values occurring in each dynamic scope. Each variable value
	 * is modified by substituting the new scope values for the old. This state
	 * is either modified or a new one created and returned, depending on
	 * whether it is mutable.
	 * 
	 * @param oldToNewSidMap
	 *            map from old dynamic scope IDs to new (-1 used for dynamic
	 *            scopes which are being removed because they are unreachable)
	 * @param modelFactory
	 *            model factory used to obtain scope values
	 * @return the new state or this, with all values updated
	 */
	private TransientState updateScopeReferences(int[] oldToNewSidMap,
			ModelFactory modelFactory) {
		SymbolicUniverse universe = modelFactory.universe();
		Map<SymbolicExpression, SymbolicExpression> scopeSubMap = scopeSubMap(
				oldToNewSidMap, modelFactory);
		ArrayList<DyscopeNode> theNodes = mutable ? scopeNodes : cloneNodes();

		for (DyscopeNode node : theNodes) {
			DynamicScope dynamicScope = node.scope;
			DynamicScope newDynamicScope = updateScopeReferences(scopeSubMap,
					universe, dynamicScope);

			if (dynamicScope != newDynamicScope)
				node.scope = newDynamicScope;
		}
		return mutable ? this : new TransientState(cloneProcStates(), theNodes,
				pathCondition);
	}

	private TransientState updateScopesInStacks(int[] map) {
		int numProcs = processStates.size();
		TransientState result = this;

		for (int i = 0; i < numProcs; i++) {
			TransientProcessState processState = (TransientProcessState) processStates
					.get(i);

			result = result.setProcessState(i, processState.updateScopes(map));
		}
		return result;
	}

	private DynamicScope updateProcReferences(
			Map<SymbolicExpression, SymbolicExpression> map,
			SymbolicUniverse universe, DynamicScope scope) {
		Scope staticScope = scope.lexicalScope();
		Collection<Variable> procVariableIter = staticScope
				.variablesWithProcrefs();

		for (Variable variable : procVariableIter) {
			int vid = variable.vid();
			SymbolicExpression oldValue = scope.getValue(vid);

			if (oldValue != null && !oldValue.isNull()) {
				SymbolicExpression newValue = universe
						.substitute(oldValue, map);

				if (oldValue != newValue)
					scope = scope.setValue(vid, newValue);
			}
		}
		return scope;
	}

	/**
	 * Replaces process references in the state as follows: a reference to
	 * process i is changed to a reference to process i-1 if i>=pid+1. A
	 * reference to process pid is changed to UNDEFINED. A reference to process
	 * i for i<pid is left unchanged. The reachers are also updated accordingly.
	 * 
	 * As usual, if this state is mutable this method will modify the state and
	 * return this. Otherwise it will create a new state and return that.
	 * 
	 * @param pid
	 *            an integer
	 * @param modelFactory
	 *            model factory used to create process reference values
	 * @return modified state
	 */
	private TransientState shiftProcReferences(int pid,
			ModelFactory modelFactory) {
		SymbolicUniverse universe = modelFactory.universe();
		Map<SymbolicExpression, SymbolicExpression> map = new HashMap<>();
		int nprocs = processStates.size();

		// nprocs is the number of procs after removing one.
		// hence highest pid that can occur in state is nprocs.
		map.put(modelFactory.processValue(pid), modelFactory.processValue(-1));
		for (int i = pid + 1; i <= nprocs; i++)
			map.put(modelFactory.processValue(i),
					modelFactory.processValue(i - 1));
		if (mutable) {
			for (DyscopeNode node : scopeNodes) {
				node.scope = updateProcReferences(map, universe, node.scope);
				shiftBitSetMutable(pid, node.reachers);
			}
			return this;
		} else {
			int n = scopeNodes.size();
			ArrayList<DyscopeNode> theNodes = new ArrayList<DyscopeNode>(n);

			for (DyscopeNode node : scopeNodes)
				theNodes.add(new DyscopeNode(node.id, updateProcReferences(map,
						universe, node.scope), null, shiftBitSet(pid,
						node.reachers)));
			for (int i = 0; i < n; i++) {
				DyscopeNode oldParent = scopeNodes.get(i).parent;

				if (oldParent != null)
					theNodes.get(i).parent = theNodes.get(oldParent.id);
			}
			return new TransientState(cloneProcStates(), theNodes,
					pathCondition);
		}
	}

	/**
	 * Modifies the bit set by setting value at position i to old value at
	 * position i+1 for i>=pid.
	 * 
	 * @param pid
	 * @param set
	 */
	private void shiftBitSetMutable(int pid, BitSet set) {
		int length = set.length();

		for (int i = pid; i < length; i++)
			set.set(i, set.get(i + 1));
	}

	/**
	 * Returns bit set obtained from original by setting value at position i to
	 * original value at position i+1 for i>=pid. Does not modify the original.
	 * 
	 * @param pid
	 *            an integer
	 * @param set
	 *            the original bit set
	 * @return new bit set modified as stated above
	 */
	private BitSet shiftBitSet(int pid, BitSet set) {
		int length = set.length();
		BitSet newSet = new BitSet(length);

		for (int i = 0; i < pid; i++)
			newSet.set(i, set.get(i));
		for (int i = pid; i < length; i++)
			newSet.set(i, set.get(i + 1));
		return newSet;
	}

	// Package private methods...

	/**
	 * Makes this instance canonic with the given canonic ID. Make all dynamic
	 * scopes and process states which are part of this state canonic as well.
	 * 
	 * The method {@link #isCanonic()} will henceforth return true, and the
	 * method {@link #getCanonicId()} will return the specified int.
	 * 
	 * Precondition: the state much be immutable (committed).
	 * 
	 * @param canonicId
	 *            the canonicID for this
	 */
	void canonize(int canonicId,
			Map<TransientObject, TransientObject> canonicMap,
			SymbolicUniverse universe) {
		int numProcs = processStates.size();

		assert !mutable;
		pathCondition = (BooleanExpression) universe.canonic(pathCondition);
		for (DyscopeNode node : scopeNodes) {
			TransientDynamicScope scope = (TransientDynamicScope) node.scope;

			if (!scope.isCanonic()) {
				DynamicScope canonicScope = (DynamicScope) canonicMap
						.get(scope);

				if (canonicScope == null) {
					scope.makeCanonic(canonicMap.size());
					canonicMap.put(scope, scope);
					canonicScope = scope;
				}
				node.scope = canonicScope;
			}
		}
		for (int i = 0; i < numProcs; i++) {
			TransientProcessState processState = (TransientProcessState) processStates
					.get(i);

			if (!processState.isCanonic()) {
				ProcessState canonicProcessState = (ProcessState) canonicMap
						.get(processState);

				if (canonicProcessState == null) {
					processState.makeCanonic(canonicMap.size());
					canonicMap.put(processState, processState);
					canonicProcessState = processState;
				}
				processStates.set(i, canonicProcessState);
			}
		}
		makeCanonic(canonicId);
	}

	/**
	 * Returns a TransientState which is equivalent to this one except that the
	 * processStates field has been replaced with the given one. If this state
	 * is mutable, this method may just modify this state and return this. If it
	 * is immutable, a new state is created and returned.
	 * 
	 * @param processStates
	 *            new value for processStates
	 * @return a state with the processStates as specified
	 */
	TransientState setProcessStates(ArrayList<ProcessState> processStates) {
		if (mutable) {
			this.processStates = processStates;
			return this;
		}
		return new TransientState(processStates, cloneNodes(), pathCondition);
	}

	TransientState setScopeNodes(ArrayList<DyscopeNode> scopeNodes) {
		if (mutable) {
			this.scopeNodes = scopeNodes;
			return this;
		}
		return new TransientState(cloneProcStates(), scopeNodes, pathCondition);
	}

	TransientState setScope(int scopeId, DynamicScope scope) {
		if (mutable) {
			scopeNodes.get(scopeId).scope = scope;
			return this;
		} else {
			ArrayList<DyscopeNode> newNodes = cloneNodes();

			newNodes.get(scopeId).scope = scope;
			return new TransientState(cloneProcStates(), newNodes,
					pathCondition);
		}
	}

	TransientState setProcessState(int index, ProcessState processState) {
		int length = this.processStates.size();

		if (index < length && processStates.get(index) == processState)
			return this;
		else {
			ArrayList<ProcessState> theProcessStates = mutable ? processStates
					: cloneProcStates();

			if (index < length) {
				theProcessStates.set(index, processState);
			} else {
				while (length < index) {
					theProcessStates.add(null);
					length++;
				}
				assert length == index;
				theProcessStates.add(processState);
				length++;
			}
			return mutable ? this : new TransientState(theProcessStates,
					cloneNodes(), pathCondition);
		}
	}

	/**
	 * Removes a process state from this state. The process states with greater
	 * pid must be shifted down, their pids must be changed.
	 * 
	 * @param pid
	 * @return
	 */
	TransientState removeProcessState(int pid, ModelFactory modelFactory) {
		int nprocs = processStates.size();
		@SuppressWarnings("unchecked")
		ArrayList<ProcessState> theProcessStates = mutable ? processStates
				: (ArrayList<ProcessState>) processStates.clone();
		TransientState result;

		theProcessStates.remove(pid);
		for (int i = pid; i < nprocs - 1; i++) {
			ProcessState processState = processStates.get(i);

			theProcessStates.set(i,
					((TransientProcessState) processState).setPid(i));
		}
		result = mutable ? this : setProcessStates(theProcessStates);
		result = result.shiftProcReferences(pid, modelFactory);
		return result;
	}

	/**
	 * Computes the set of reachable scopes, reorders them in a canonical way,
	 * eliminates the unreachable ones, and updates all scope references in
	 * state.
	 * 
	 * @param modelFactory
	 *            model factory, needed to get scope values
	 * @return the state with the scopes modified, either this one (if mutable)
	 *         or a new one (if immutable)
	 */
	TransientState collectScopes(ModelFactory modelFactory) {
		Pair<int[], Integer> renumberInfo = numberScopes();
		int[] map = renumberInfo.left;
		int newNumScopes = renumberInfo.right;
		TransientState result;

		if (mutable) {
			int[] inverseMap = Transmuter.inverse(map, newNumScopes);

			Transmuter.transmuteInPlace(map, inverseMap, scopeNodes);
			for (int i = 0; i < newNumScopes; i++)
				scopeNodes.get(i).id = i;
			result = this;
		} else {
			ArrayList<DyscopeNode> newScopeNodes = new ArrayList<>(newNumScopes);
			int length = 0;
			int n = scopeNodes.size();

			for (int i = 0; i < n; i++) {
				DyscopeNode oldNode = scopeNodes.get(i);
				int j = map[i];

				if (j >= 0) {
					DyscopeNode newNode = new DyscopeNode(j, oldNode.scope,
							null, oldNode.reachers);

					if (j < length) {
						newScopeNodes.set(j, newNode);
					} else {
						while (j > length) {
							newScopeNodes.add(null);
							length++;
						}
						assert length == j;
						newScopeNodes.add(newNode);
						length++;
					}
				}
			}
			assert length == newNumScopes;
			for (int i = 0; i < n; i++) {
				DyscopeNode oldNode = scopeNodes.get(i);
				int j = map[i];

				if (j >= 0) {
					DyscopeNode newNode = newScopeNodes.get(j);
					DyscopeNode oldParent = oldNode.parent;

					if (oldParent != null) {
						int newParentId = map[oldParent.id];

						assert newParentId >= 0;
						assert newParentId < newNumScopes;
						newNode.parent = newScopeNodes.get(newParentId);
					}
				}
			}
			result = this.setScopeNodes(newScopeNodes);
		}
		result = result.updateScopeReferences(map, modelFactory);
		result = result.updateScopesInStacks(map);
		return result;
	}

	TransientState addScope(DynamicScope scope, int parentId, BitSet reachers) {
		int id = scopeNodes.size();
		ArrayList<DyscopeNode> theNodes = mutable ? scopeNodes
				: cloneNodes(id + 1);

		theNodes.add(new DyscopeNode(id, scope, parentId < 0 ? null
				: scopeNodes.get(parentId), reachers));
		return mutable ? this : new TransientState(cloneProcStates(), theNodes,
				pathCondition);
	}

	/**
	 * Changes the location of the top frame on the specified process' call
	 * stack.
	 * 
	 * As always, the mutability of this state and the process state is
	 * respected, so that immutable instances will not be modified.
	 * 
	 * Preconditions: (1) the call stack must be non-empty; (2) the top frame of
	 * the call stack must have a dynamic scope for which the corresponding
	 * static scope contains the given location.
	 * 
	 * @param pid
	 *            the PID of a process in this state
	 * @param location
	 *            a location in the static scope corresponding to the dynamic
	 *            scope of the top frame of the call stack of the specified
	 *            process
	 * @return a state with top frame of call stack of process modified to
	 *         reflect the new location
	 */
	TransientState setLocation(int pid, Location location) {
		TransientProcessState processState = (TransientProcessState) processStates
				.get(pid);
		TransientProcessState newProcessState = processState
				.setLocation(location);

		return setProcessState(pid, newProcessState);
	}

	/**
	 * Replaces the top entry of the specified process' call stack with the
	 * given frame.
	 * 
	 * Preconditions: pid must be the PID of a process in this state with a
	 * non-empty call stack.
	 * 
	 * As usual, this method respects mutability.
	 * 
	 * @param pid
	 *            PID of a process in this state
	 * @param newStackEntry
	 *            new activation frame to replace the top one
	 * @return state with process state modified as specified
	 */
	TransientState replaceTop(int pid, TransientStackEntry newStackEntry) {
		TransientProcessState processState = (TransientProcessState) processStates
				.get(pid);
		TransientProcessState newProcessState = processState
				.replaceTop(newStackEntry);

		return setProcessState(pid, newProcessState);
	}

	TransientState setReachable(int pid, int dyscopeId, boolean value) {
		if (mutable) {
			scopeNodes.get(dyscopeId).reachers.set(pid, value);
			return this;
		} else {
			ArrayList<DyscopeNode> theNodes = cloneNodes();

			theNodes.get(dyscopeId).reachers.set(pid, value);
			return new TransientState(cloneProcStates(), theNodes,
					pathCondition);
		}
	}

	TransientState push(int pid, StackEntry entry) {
		TransientProcessState processState = (TransientProcessState) processStates
				.get(pid);
		ProcessState newProcessState = processState.push(entry);

		return setProcessState(pid, newProcessState);
	}

	TransientState pop(int pid) {
		TransientProcessState processState = (TransientProcessState) processStates
				.get(pid);
		ProcessState newProcessState = processState.pop();

		return setProcessState(pid, newProcessState);
	}

	// Public methods...

	public DynamicScope getParentScope(int scopeId) {
		DyscopeNode parent = scopeNodes.get(scopeId).parent;

		return parent == null ? null : parent.scope;
	}

	public DynamicScope getScope(int pid, Variable variable) {
		int dycopeId = getProcessState(pid).getDyscopeId();
		DyscopeNode node = scopeNodes.get(dycopeId);
		Scope variableScope = variable.scope();

		while (node != null) {
			if (node.scope.lexicalScope() == variableScope)
				return node.scope;
			node = node.parent;
		}
		throw new IllegalArgumentException("Variable not in scope: " + variable);
	}

	/**
	 * @return The system scope.
	 */
	public DynamicScope rootScope() {
		return scopeNodes.get(0).scope;
	}

	@Override
	protected int computeHashCode() {
		int result = pathCondition.hashCode();

		for (ProcessState processState : processStates)
			result ^= processState.hashCode();
		for (DyscopeNode node : scopeNodes)
			result ^= node.hashCode();
		return result;
	}

	@Override
	protected boolean computeEquals(Object object) {
		if (object instanceof TransientState) {
			TransientState that = (TransientState) object;

			if (!pathCondition.equals(that.pathCondition))
				return false;
			if (processStates.size() != that.processStates.size())
				return false;
			if (scopeNodes.size() != that.scopeNodes.size())
				return false;
			else {
				Iterator<ProcessState> iter1 = processStates.iterator();
				Iterator<ProcessState> iter2 = that.processStates.iterator();

				while (iter1.hasNext())
					if (!iter1.next().equals(iter2.next()))
						return false;

				Iterator<DyscopeNode> iter3 = scopeNodes.iterator();
				Iterator<DyscopeNode> iter4 = that.scopeNodes.iterator();

				while (iter3.hasNext())
					if (!iter3.next().equals(iter4.next()))
						return false;
				return true;
			}
		}
		return false;
	}

	// Public methods implementing State...

	/**
	 * The number of scopes, including blanks.
	 * 
	 * @return
	 */
	@Override
	public int numScopes() {
		return scopeNodes.size();
	}

	/**
	 * The number of processes, including blanks.
	 * 
	 * @return
	 */
	@Override
	public int numProcs() {
		return processStates.size();
	}

	@Override
	public void commit() {
		if (!mutable)
			return;
		scopeNodes.trimToSize();
		processStates.trimToSize();
		for (DyscopeNode node : scopeNodes)
			// if (node != null && node.scope != null)
			((Transient) node.scope).commit();
		for (ProcessState processState : processStates)
			if (processState != null)
				((Transient) processState).commit();
		mutable = false;
	}

	@Override
	public TransientState setPathCondition(BooleanExpression pathCondition) {
		if (mutable) {
			this.pathCondition = pathCondition;
			return this;
		}
		return new TransientState(cloneProcStates(), cloneNodes(),
				pathCondition);
	}

	/**
	 * @param pid
	 *            A process ID.
	 * @return The process associated with the ID. if non-existent.
	 * 
	 */
	@Override
	public ProcessState getProcessState(int pid) {
		return processStates.get(pid);
	}

	/**
	 * @return The system scope id.
	 * 
	 */
	@Override
	public int rootScopeID() {
		return 0;
	}

	/**
	 * @return The path condition.
	 */
	@Override
	public BooleanExpression getPathCondition() {
		return pathCondition;
	}

	/**
	 * @return Whether this state has been seen in the depth first search.
	 */
	@Override
	public boolean seen() {
		return seen;
	}

	/**
	 * @return Whether this state is on the DFS stack.
	 */
	@Override
	public boolean onStack() {
		return onStack;
	}

	/**
	 * @param seen
	 *            Whether this state has been seen in the depth first search.
	 */
	@Override
	public void setSeen(boolean seen) {
		this.seen = seen;
	}

	/**
	 * @param onStack
	 *            Whether this state is on the DFS stack.
	 */
	@Override
	public void setOnStack(boolean onStack) {
		this.onStack = onStack;
	}

	/**
	 * Given the id of a scope, return that dynamic scope.
	 * 
	 * @param id
	 *            The dynamic scope id number.
	 * @return The corresponding dynamic scope.
	 */
	@Override
	public TransientDynamicScope getScope(int id) {
		return (TransientDynamicScope) scopeNodes.get(id).scope;
	}

	@Override
	public int getParentId(int scopeId) {
		DyscopeNode parent = scopeNodes.get(scopeId).parent;

		return parent == null ? -1 : parent.id;
	}

	@Override
	public int getScopeId(int pid, Variable variable) {
		int scopeId = getProcessState(pid).getDyscopeId();
		DynamicScope scope;

		while (scopeId >= 0) {
			scope = getScope(scopeId);
			if (scope.lexicalScope().variables().contains(variable))
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

	// Structure:
	// State 45
	// 1. Scopes
	// 1.1. scope 45 (: null) (parent = 46)
	// 1.1.1. x = 27
	// 2. Processes
	// 2.1. process 0 (: null) or call stack
	// 2.1.1 [location=locationID,scope=dynamicScopeId] (top)
	// 3. Buffers
	// 3.1. 3->4
	// 3.1.1 Message 0
	// 3.1.1.1 tag=
	// 3.1.1.2 data=
	@Override
	public void print(PrintStream out) {
		int numProcs = numProcs();

		out.print("State " + identifier());
		out.println();
		out.println("| Path condition");
		out.println("| | " + pathCondition);
		out.println("| Dynamic scopes");
		for (DyscopeNode node : scopeNodes) {
			node.print(out, "| | ");
		}
		out.println("| Process states");
		for (int i = 0; i < numProcs; i++) {
			ProcessState process = processStates.get(i);

			if (process == null)
				out.println("| | process " + i + ": null");
			else
				process.print(out, "| | ");
		}
		out.flush();
	}

	@Override
	public String toString() {
		return "State " + identifier();
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
	public Iterable<ProcessState> getProcessStates() {
		return processStates;
	}

	@Override
	public int numberOfReachers(int sid) {
		return scopeNodes.get(sid).reachers.cardinality();
	}

	@Override
	public boolean reachableByProcess(int sid, int pid) {
		return scopeNodes.get(sid).reachers.get(pid);
	}

	@Override
	public TransientState setVariable(int vid, int scopeId,
			SymbolicExpression value) {
		TransientDynamicScope scope = getScope(scopeId);

		if (scope.isMutable()) { // state is also mutable
			scope.setValue(vid, value);
			return this;
		} else {
			return setScope(scopeId, scope.setValue(vid, value));
		}
	}

}
