package edu.udel.cis.vsl.civl.state.immutable;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.run.UserInterface;
import edu.udel.cis.vsl.civl.semantics.Evaluator;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.StackEntry;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.gmc.GMCConfiguration;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * An implementation of StateFactory based on the Immutable Pattern.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * @author Timothy J. McClory (tmcclory)
 * @author Stephen F. Siegel (siegel)
 * 
 */
public class ImmutableStateFactory implements StateFactory {

	/************************* Instance Fields *************************/

	private GMCConfiguration config;

	private Evaluator evaluator;

	private boolean simplify;

	private long initialNumStateInstances = ImmutableState.instanceCount;

	private ModelFactory modelFactory;

	private Map<ImmutableProcessState, ImmutableProcessState> processMap = new HashMap<>(
			100000);

	private Map<ImmutableDynamicScope, ImmutableDynamicScope> scopeMap = new HashMap<>(
			100000);

	private int stateCount = 0;

	private Map<ImmutableState, ImmutableState> stateMap = new HashMap<>(
			1000000);

	private Reasoner trueReasoner;

	private SymbolicUniverse universe;

	/* **************************** Constructors *************************** */

	/**
	 * Factory to create all state objects.
	 */
	public ImmutableStateFactory(ModelFactory modelFactory,
			GMCConfiguration config) {
		this.modelFactory = modelFactory;
		this.config = config;
		this.universe = modelFactory.universe();
		this.trueReasoner = universe.reasoner(universe.trueExpression());
		this.simplify = config.isTrue(UserInterface.simplifyO);
	}

	/* *************************** Private Methods ************************* */

	/**
	 * Creates a dynamic scope in its initial state.
	 * 
	 * @param lexicalScope
	 *            The lexical scope corresponding to this dynamic scope.
	 * @param parent
	 *            The parent of this dynamic scope. -1 only for the topmost
	 *            dynamic scope.
	 * @return A new dynamic scope.
	 */
	private ImmutableDynamicScope initialDynamicScope(Scope lexicalScope,
			int parent, int dynamicScopeId, BitSet reachers) {
		return new ImmutableDynamicScope(lexicalScope, parent, initialValues(
				lexicalScope, dynamicScopeId), reachers);
	}

	private SymbolicExpression[] initialValues(Scope lexicalScope,
			int dynamicScopeId) {
		// TODO: special handling for input variables in root scope?
		SymbolicExpression[] values = new SymbolicExpression[lexicalScope
				.variables().size()];

		for (int i = 0; i < values.length; i++) {
			values[i] = universe.nullExpression();
		}
		return values;
	}

	/**
	 * Given two static scopes, this method computes a non-empty sequence of
	 * scopes with the following properties:
	 * <ul>
	 * <li>The first (0-th) element of the sequence is the join of scope1 and
	 * scope2.</li>
	 * <li>The last element is scope2.</li>
	 * <li>For each i (0<=i<length-1), the i-th element is the parent of the
	 * (i+1)-th element.</li>
	 * </ul>
	 * 
	 * @param scope1
	 *            a static scope
	 * @param scope2
	 *            a static scope
	 * @return join sequence as described above
	 * 
	 * @exception IllegalArgumentException
	 *                if the scopes do not have a common ancestor
	 */
	private Scope[] joinSequence(Scope scope1, Scope scope2) {
		if (scope1 == scope2)
			return new Scope[] { scope2 };
		for (Scope scope1a = scope1; scope1a != null; scope1a = scope1a
				.parent())
			for (Scope scope2a = scope2; scope2a != null; scope2a = scope2a
					.parent())
				if (scope1a.equals(scope2a)) {
					Scope join = scope2a;
					int length = 1;
					Scope[] result;
					Scope s;

					for (s = scope2; s != join; s = s.parent())
						length++;
					result = new Scope[length];
					s = scope2;
					for (int i = length - 1; i >= 0; i--) {
						result[i] = s;
						s = s.parent();
					}
					return result;
				}
		throw new IllegalArgumentException("No common scope:\n" + scope1 + "\n"
				+ scope2);
	}

	/**
	 * Numbers the reachable dynamic scopes in a state in a canonical way.
	 * Scopes are numbered from 0 up, in the order in which they are encountered
	 * by iterating over the processes by increasing ID, iterating over the
	 * process' call stack frames from index 0 up, iterating over the parent
	 * scopes from the scope referenced by the frame.
	 * 
	 * Unreachable scopes are assigned the number -1.
	 * 
	 * Returns an array which of length numScopes in which the element at
	 * position i is the new ID number for the scope whose old ID number is i.
	 * Does not modify anything.
	 * 
	 * @param state
	 *            a state
	 * @return an array mapping old scope IDs to new.
	 */
	private int[] numberScopes(ImmutableState state) {
		int numScopes = state.numScopes();
		int numProcs = state.numProcs();
		int[] oldToNew = new int[numScopes];

		// the root dyscope is forced to be 0
		oldToNew[0] = 0;

		int nextScopeId = 1;
		for (int i = 1; i < numScopes; i++)
			oldToNew[i] = -1;
		for (int pid = 0; pid < numProcs; pid++) {
			ImmutableProcessState process = state.getProcessState(pid);
			int stackSize;

			if (process == null)
				continue;
			stackSize = process.stackSize();
			// start at bottom of stack so system scope in proc 0
			// is reached first
			for (int i = stackSize - 1; i >= 0; i--) {
				int dynamicScopeId = process.getStackEntry(i).scope();

				while (oldToNew[dynamicScopeId] < 0) {
					oldToNew[dynamicScopeId] = nextScopeId;
					nextScopeId++;
					dynamicScopeId = state.getParentId(dynamicScopeId);
					if (dynamicScopeId < 0)
						break;
				}
			}
		}
		return oldToNew;
	}

	private boolean nsat(BooleanExpression p) {
		return trueReasoner.isValid(universe.not(p));
	}

	private Map<SymbolicExpression, SymbolicExpression> procSubMap(
			int[] oldToNewPidMap) {
		int size = oldToNewPidMap.length;
		Map<SymbolicExpression, SymbolicExpression> result = new HashMap<SymbolicExpression, SymbolicExpression>(
				size);

		for (int i = 0; i < size; i++) {
			SymbolicExpression oldVal = modelFactory.processValue(i);
			SymbolicExpression newVal = modelFactory
					.processValue(oldToNewPidMap[i]);

			result.put(oldVal, newVal);
		}
		return result;
	}

	/**
	 * General method for pushing a frame onto a call stack, whether or not the
	 * call stack is for a new process (and therefore empty).
	 * 
	 * @param state
	 *            the initial state
	 * @param pid
	 *            the PID of the process whose stack is to be modified; this
	 *            stack may be empty
	 * @param function
	 *            the called function that will be pushed onto the stack
	 * @param arguments
	 *            the arguments to the function
	 * @param callerPid
	 *            the PID of the process that is creating the new frame. For an
	 *            ordinary function call, this will be the same as pid. For a
	 *            "spawn" command, callerPid will be different from pid and
	 *            process pid will be new and have an empty stack. Exception: if
	 *            callerPid is -1 then the new dynamic scope will have no
	 *            parent; this is used for pushing the original system function,
	 *            which has no caller
	 * @return new stack with new frame on call stack of process pid
	 */
	private ImmutableState pushCallStack2(ImmutableState state, int pid,
			CIVLFunction function, SymbolicExpression[] arguments, int callerPid) {
		Scope containingStaticScope = function.containingScope();
		Scope functionStaticScope = function.outerScope();
		ImmutableProcessState[] newProcesses = state.copyProcessStates();
		int numScopes = state.numScopes();
		SymbolicExpression[] values;
		ImmutableDynamicScope[] newScopes;
		int sid;
		int containingDynamicScopeId;
		BitSet bitSet = new BitSet(newProcesses.length);

		if (callerPid >= 0) {
			ProcessState caller = state.getProcessState(callerPid);
			ImmutableDynamicScope containingDynamicScope;

			if (caller.stackSize() == 0)
				throw new IllegalArgumentException(
						"Calling process has empty stack: " + callerPid);
			containingDynamicScopeId = caller.getDyscopeId();
			while (containingDynamicScopeId >= 0) {
				containingDynamicScope = (ImmutableDynamicScope) state
						.getScope(containingDynamicScopeId);
				if (containingStaticScope == containingDynamicScope
						.lexicalScope())
					break;
				containingDynamicScopeId = state
						.getParentId(containingDynamicScopeId);
			}
			if (containingDynamicScopeId < 0)
				throw new IllegalArgumentException(
						"Called function not visible:\nfunction: " + function
								+ "\npid: " + pid + "\ncallerPid:" + callerPid
								+ "\narguments: " + arguments);
		} else {
			containingDynamicScopeId = -1;
		}
		newScopes = state.copyAndExpandScopes();
		sid = numScopes;
		values = initialValues(functionStaticScope, sid);
		for (int i = 0; i < arguments.length; i++)
			if (arguments[i] != null)
				values[i] = arguments[i];
		bitSet.set(pid);
		newScopes[sid] = new ImmutableDynamicScope(functionStaticScope,
				containingDynamicScopeId, values, bitSet);
		{
			int id = containingDynamicScopeId;
			ImmutableDynamicScope scope;

			while (id >= 0) {
				scope = newScopes[id];
				bitSet = newScopes[id].getReachers();
				if (bitSet.get(pid))
					break;
				bitSet = (BitSet) bitSet.clone();
				bitSet.set(pid);
				newScopes[id] = scope.setReachers(bitSet);
				id = scope.getParent();
			}
		}
		newProcesses[pid] = state.getProcessState(pid).push(
				stackEntry(null, sid));
		state = new ImmutableState(newProcesses, newScopes,
				state.getPathCondition());
		state = setLocation(state, pid, function.startLocation());
		return state;
	}

	private Map<SymbolicExpression, SymbolicExpression> scopeSubMap(
			int[] oldToNewSidMap) {
		int size = oldToNewSidMap.length;
		Map<SymbolicExpression, SymbolicExpression> result = new HashMap<SymbolicExpression, SymbolicExpression>(
				size);

		for (int i = 0; i < size; i++) {
			SymbolicExpression oldVal = modelFactory.scopeValue(i);
			SymbolicExpression newVal = modelFactory
					.scopeValue(oldToNewSidMap[i]);

			result.put(oldVal, newVal);
		}
		return result;
	}

	/**
	 * Given an array of dynamic scopes and a process state, computes the actual
	 * dynamic scopes reachable from that process and modifies the array as
	 * necessary by replacing a dynamic scope with a scope that is equivalent
	 * except for the corrected bit set.
	 * 
	 * @param dynamicScopes
	 *            an array of dynamic scopes, to be modified
	 * @param process
	 *            a process state
	 */
	private void setReachablesForProc(ImmutableDynamicScope[] dynamicScopes,
			ImmutableProcessState process) {
		int stackSize = process.stackSize();
		int numScopes = dynamicScopes.length;
		boolean reached[] = new boolean[numScopes];
		int pid = process.getPid();

		for (int i = 0; i < stackSize; i++) {
			StackEntry frame = process.getStackEntry(i);
			int id = frame.scope();

			while (id >= 0) {
				if (reached[id])
					break;
				reached[id] = true;
				id = dynamicScopes[id].getParent();
			}
		}
		for (int j = 0; j < numScopes; j++) {
			ImmutableDynamicScope scope = dynamicScopes[j];
			BitSet bitSet = scope.getReachers();

			if (bitSet.get(pid) != reached[j]) {
				BitSet newBitSet = (BitSet) bitSet.clone();

				newBitSet.flip(pid);
				dynamicScopes[j] = dynamicScopes[j].setReachers(newBitSet);
			}
		}
	}

	/**
	 * Create a new call stack entry.
	 * 
	 * @param location
	 *            The location to go to after returning from this call.
	 * @param scope
	 *            The dynamic scope the process is in before the call.
	 * @param lhs
	 *            The location to store the return value. Null if non-existent.
	 */
	private ImmutableStackEntry stackEntry(Location location, int scope) {
		return new ImmutableStackEntry(location, scope);
	}

	/**
	 * Given a BitSet indexed by process IDs, and a map of old PIDs to new PIDs,
	 * returns a BitSet equivalent to original but indexed using the new PIDs.
	 * 
	 * If no changes are made, the original BitSet (oldBitSet) is returned.
	 * 
	 * @param oldBitSet
	 * @param oldToNewPidMap
	 *            array of length state.numProcs in which element at index i is
	 *            the new PID of the process whose old PID is i. A negative
	 *            value indicates that the process of (old) PID i is to be
	 *            removed.
	 * @return
	 */
	private BitSet updateBitSet(BitSet oldBitSet, int[] oldToNewPidMap) {
		BitSet newBitSet = null;
		int length = oldBitSet.length();

		for (int i = 0; i < length; i++) {
			boolean flag = oldBitSet.get(i);

			if (flag) {
				int newIndex = oldToNewPidMap[i];

				if (newIndex >= 0) {
					if (newBitSet == null)
						newBitSet = new BitSet(length);
					newBitSet.set(newIndex);
				}
			}
		}
		if (newBitSet == null)
			return oldBitSet;
		return newBitSet;
	}

	/**
	 * Searches the dynamic scopes in the given state for any process reference
	 * value, and returns a new array of scopes equivalent to the old except
	 * that those process reference values have been replaced with new specified
	 * values. Used for garbage collection and canonicalization of PIDs.
	 * 
	 * Also updates the reachable BitSet in each DynamicScope: create a new
	 * BitSet called newReachable. iterate over all entries in old BitSet
	 * (reachable). If old entry is position i is true, set oldToNewPidMap[i] to
	 * true in newReachable (assuming oldToNewPidMap[i]>=0).
	 * 
	 * The method returns null if no changes were made.
	 * 
	 * @param state
	 *            a state
	 * @param oldToNewPidMap
	 *            array of length state.numProcs in which element at index i is
	 *            the new PID of the process whose old PID is i. A negative
	 *            value indicates that the process of (old) PID i is to be
	 *            removed.
	 * @return new dyanmic scopes or null
	 */
	private ImmutableDynamicScope[] updateProcessReferencesInScopes(
			ImmutableState state, int[] oldToNewPidMap) {
		Map<SymbolicExpression, SymbolicExpression> procSubMap = procSubMap(oldToNewPidMap);
		ImmutableDynamicScope[] newScopes = null;
		int numScopes = state.numScopes();

		for (int i = 0; i < numScopes; i++) {
			ImmutableDynamicScope dynamicScope = state.getScope(i);
			Scope staticScope = dynamicScope.lexicalScope();
			Collection<Variable> procrefVariableIter = staticScope
					.variablesWithProcrefs();
			SymbolicExpression[] newValues = null;
			BitSet oldBitSet = dynamicScope.getReachers();
			BitSet newBitSet = updateBitSet(oldBitSet, oldToNewPidMap);
			Model model = staticScope.model();

			for (Variable variable : procrefVariableIter) {
				int vid = variable.vid();
				SymbolicExpression oldValue = dynamicScope.getValue(vid);
				SymbolicExpression newValue = universe.substitute(oldValue,
						procSubMap);

				// update communicator
				if (variable.type().equals(model.commType())) {
					SymbolicExpression procMatrix = this.universe.tupleRead(
							newValue, universe.intObject(1));
					NumericExpression symbolicRankCount = ((SymbolicCompleteArrayType) procMatrix
							.type()).extent();
					int rankCount = evaluator.extractInt(null,
							symbolicRankCount);
					SymbolicExpression undefinedProc = modelFactory
							.undefinedProcessValue();
					int procCount = 0;
					 ArrayList<SymbolicExpression> newProcQueueArrayComponents
					 = new ArrayList<>();
					SymbolicExpression newProcQueueArray = procMatrix;
					 SymbolicTupleType newProcQueueType = null;
					// SymbolicExpression buffer = universe.tupleRead(newValue,
					// universe.intObject(2));
					SymbolicExpression newComm;
					// ArrayList<SymbolicExpression> newCommComponents = new
					// ArrayList<>();

					for (int rank = 0; rank < rankCount; rank++) {
						SymbolicExpression procQueue = this.universe.arrayRead(
								procMatrix, universe.integer(rank));
						int procRowLength = evaluator.extractInt(null,
								(NumericExpression) universe.tupleRead(
										procQueue, universe.intObject(0)));
						SymbolicExpression procRow = universe.tupleRead(
								procQueue, universe.intObject(1));
						ArrayList<SymbolicExpression> newProcQueueComponents = new ArrayList<>();
						ArrayList<SymbolicType> newProcQueueTypeComponents = new ArrayList<>();
						ArrayList<SymbolicExpression> newProcArrayComponents = new ArrayList<>();
						SymbolicExpression newProcArray, newProcQueue;
						int procQueueLength = 0;

						for (int j = 0; j < procRowLength; j++) {
							SymbolicExpression proc = universe.arrayRead(
									procRow, universe.integer(j));

							if (!proc.equals(undefinedProc)) {
								newProcArrayComponents.add(proc);
								procCount++;
								procQueueLength++;
							}
						}
						newProcArray = universe.array(
								modelFactory.processSymbolicType(),
								newProcArrayComponents);
						newProcQueueComponents.add(universe.integer(procQueueLength));
						newProcQueueComponents.add(newProcArray);
						newProcQueueTypeComponents.add(universe.integerType());
						newProcQueueTypeComponents.add(newProcArray.type());
						newProcQueueType = universe.tupleType(universe.stringObject("__procQueue__"), newProcQueueTypeComponents);
						newProcQueue = universe.tuple(newProcQueueType, newProcQueueComponents);
						newProcQueueArrayComponents.add(newProcQueue);
					}
					newProcQueueArray = universe.array(universe.pureType(newProcQueueType), newProcQueueArrayComponents);
					newComm = universe.tupleWrite(newValue,
							universe.intObject(0), universe.integer(procCount));
					newComm = universe.tupleWrite(newComm,
							universe.intObject(1), newProcQueueArray);
					newValue = newComm;
				}

				if (oldValue != newValue) {
					if (newValues == null)
						newValues = dynamicScope.copyValues();
					newValues[vid] = newValue;
				}
			}
			if (newValues != null || newBitSet != oldBitSet) {
				if (newScopes == null) {
					newScopes = new ImmutableDynamicScope[numScopes];
					for (int j = 0; j < i; j++)
						newScopes[j] = state.getScope(j);
				}
				if (newValues == null)
					newScopes[i] = dynamicScope.setReachers(newBitSet);
				else
					newScopes[i] = new ImmutableDynamicScope(staticScope,
							dynamicScope.getParent(), newValues, newBitSet);
			} else if (newScopes != null) {
				newScopes[i] = dynamicScope;
			}
		}
		return newScopes;
	}

	public ImmutableState simplifyWork(ImmutableState theState) {
		int numScopes = theState.numScopes();
		BooleanExpression pathCondition = theState.getPathCondition();
		ImmutableDynamicScope[] newDynamicScopes = null;
		Reasoner reasoner = universe.reasoner(pathCondition);
		BooleanExpression newPathCondition;

		for (int i = 0; i < numScopes; i++) {
			ImmutableDynamicScope oldScope = theState.getScope(i);
			int numVars = oldScope.numberOfVariables();
			SymbolicExpression[] newVariableValues = null;

			for (int j = 0; j < numVars; j++) {
				SymbolicExpression oldValue = oldScope.getValue(j);
				SymbolicExpression newValue = reasoner.simplify(oldValue);

				if (oldValue != newValue && newVariableValues == null) {
					newVariableValues = new SymbolicExpression[numVars];
					for (int j2 = 0; j2 < j; j2++)
						newVariableValues[j2] = oldScope.getValue(j2);
				}
				if (newVariableValues != null)
					newVariableValues[j] = newValue;
			}
			if (newVariableValues != null && newDynamicScopes == null) {
				newDynamicScopes = new ImmutableDynamicScope[numScopes];
				for (int i2 = 0; i2 < i; i2++)
					newDynamicScopes[i2] = theState.getScope(i2);
			}
			if (newDynamicScopes != null)
				newDynamicScopes[i] = newVariableValues != null ? oldScope
						.setVariableValues(newVariableValues) : oldScope;
		}
		newPathCondition = reasoner.getReducedContext();
		if (newPathCondition != pathCondition) {
			if (nsat(newPathCondition))
				newPathCondition = universe.falseExpression();
		} else
			newPathCondition = null;
		if (newDynamicScopes != null || newPathCondition != null) {
			theState = ImmutableState.newState(theState, null,
					newDynamicScopes, newPathCondition);
			theState.simplifiedState = theState;
		}
		return theState;
	}

	private ImmutableState flyweight(State state) {
		ImmutableState theState = (ImmutableState) state;

		if (theState.isCanonic())
			return theState;
		else {
			ImmutableState result = stateMap.get(theState);

			if (result == null) {
				result = theState;
				result.makeCanonic(stateCount, universe, scopeMap, processMap);
				stateCount++;
				stateMap.put(result, result);
			}
			return result;
		}
	}

	/* ********************** Methods from StateFactory ******************** */

	@Override
	public ImmutableState addProcess(State state, CIVLFunction function,
			SymbolicExpression[] arguments, int callerPid) {
		ImmutableState theState = (ImmutableState) state;
		int numProcs = theState.numProcs();
		ImmutableProcessState[] newProcesses;

		newProcesses = theState.copyAndExpandProcesses();
		newProcesses[numProcs] = new ImmutableProcessState(numProcs);
		theState = theState.setProcessStates(newProcesses);
		return pushCallStack2(theState, numProcs, function, arguments,
				callerPid);
	}

	/**
	 * In this implementation of canonic: process states are collected, dynamic
	 * scopes are collected, the flyweight representative is taken, simplify is
	 * called if that option is selected, then the flyweight representative is
	 * taken again.
	 */
	@Override
	public ImmutableState canonic(State state) {
		ImmutableState theState = (ImmutableState) state;

		theState = collectProcesses(theState);
		theState = collectScopes(theState);
		theState = flyweight(theState);
		if (simplify)
			theState = simplify(theState);
		return theState;
	}

	@Override
	public ImmutableState collectScopes(State state) {
		ImmutableState theState = (ImmutableState) state;
		int oldNumScopes = theState.numScopes();
		int[] oldToNew = numberScopes(theState);
		boolean change = false;
		int newNumScopes = 0;

		for (int i = 0; i < oldNumScopes; i++) {
			int id = oldToNew[i];

			if (id >= 0)
				newNumScopes++;
			if (!change && id != i)
				change = true;
		}
		if (change) {
			Map<SymbolicExpression, SymbolicExpression> scopeSubMap = scopeSubMap(oldToNew);
			ImmutableDynamicScope[] newScopes = new ImmutableDynamicScope[newNumScopes];
			int numProcs = theState.numProcs();
			ImmutableProcessState[] newProcesses = new ImmutableProcessState[numProcs];

			for (int i = 0; i < oldNumScopes; i++) {
				int newId = oldToNew[i];

				if (newId >= 0) {
					ImmutableDynamicScope oldScope = theState.getScope(i);
					int oldParent = oldScope.getParent();

					newScopes[newId] = oldScope.updateDyscopeIds(scopeSubMap,
							universe, oldParent < 0 ? oldParent
									: oldToNew[oldParent]);
				}
			}
			for (int pid = 0; pid < numProcs; pid++)
				newProcesses[pid] = theState.getProcessState(pid)
						.updateDyscopes(oldToNew);
			theState = ImmutableState.newState(theState, newProcesses,
					newScopes, null);
		}
		return theState;
	}

	@Override
	public State getAtomicLock(State state, int pid) {
		return this.setVariable(state, 0, 0, modelFactory.processValue(pid));
	}

	@Override
	public long getNumStateInstances() {
		return ImmutableState.instanceCount - initialNumStateInstances;
	}

	@Override
	public int getNumStatesSaved() {
		return stateMap.size();
	}

	@Override
	public ImmutableState initialState(Model model) {
		ImmutableState state = new ImmutableState(new ImmutableProcessState[0],
				new ImmutableDynamicScope[0], universe.trueExpression());
		CIVLFunction function = model.system();
		int numArgs = function.parameters().size();
		SymbolicExpression[] arguments = new SymbolicExpression[numArgs];

		// TODO: how to initialize the arguments to system function?
		state = addProcess(state, function, arguments, -1);
		state = this.setVariable(state, 0, 0, modelFactory.processValue(-1));
		return canonic(state);
	}

	@Override
	public boolean lockedByAtomic(State state) {
		SymbolicExpression symbolicAtomicPid = state.getVariableValue(0, 0);
		int atomicPid = modelFactory.getProcessId(modelFactory.systemSource(),
				symbolicAtomicPid);

		return atomicPid >= 0;
	}

	@Override
	public ImmutableState popCallStack(State state, int pid) {
		ImmutableState theState = (ImmutableState) state;
		ImmutableProcessState process = theState.getProcessState(pid);
		ImmutableProcessState[] processArray = theState.copyProcessStates();
		ImmutableDynamicScope[] newScopes = theState.copyScopes();

		processArray[pid] = process.pop();
		setReachablesForProc(newScopes, processArray[pid]);
		theState = new ImmutableState(processArray, newScopes,
				theState.getPathCondition());
		return theState;
	}

	@Override
	public int processInAtomic(State state) {
		SymbolicExpression symbolicAtomicPid = state.getVariableValue(0, 0);

		return modelFactory.getProcessId(modelFactory.systemSource(),
				symbolicAtomicPid);
	}

	@Override
	public ImmutableState pushCallStack(State state, int pid,
			CIVLFunction function, SymbolicExpression[] arguments) {
		return pushCallStack2((ImmutableState) state, pid, function, arguments,
				pid);
	}

	@Override
	public ImmutableState collectProcesses(State state) {
		ImmutableState theState = (ImmutableState) state;
		int numProcs = theState.numProcs();
		boolean change = false;
		int counter = 0;

		while (counter < numProcs) {
			if (theState.getProcessState(counter) == null) {
				change = true;
				break;
			}
			counter++;
		}
		if (change) {
			int newNumProcs = counter;
			int[] oldToNewPidMap = new int[numProcs];
			ImmutableProcessState[] newProcesses;
			ImmutableDynamicScope[] newScopes;

			for (int i = 0; i < counter; i++)
				oldToNewPidMap[i] = i;
			oldToNewPidMap[counter] = -1;
			for (int i = counter + 1; i < numProcs; i++) {
				if (theState.getProcessState(i) == null) {
					oldToNewPidMap[i] = -1;
				} else {
					oldToNewPidMap[i] = newNumProcs;
					newNumProcs++;
				}
			}
			newProcesses = new ImmutableProcessState[newNumProcs];
			for (int i = 0; i < numProcs; i++) {
				int newPid = oldToNewPidMap[i];

				if (newPid >= 0)
					newProcesses[newPid] = theState.getProcessState(i).setPid(
							newPid);
			}
			newScopes = updateProcessReferencesInScopes(theState,
					oldToNewPidMap);
			theState = ImmutableState.newState(theState, newProcesses,
					newScopes, null);
		}
		return theState;
	}

	@Override
	public ImmutableState removeProcess(State state, int pid) {
		ImmutableState theState = (ImmutableState) state;

		theState = theState.setProcessState(pid, null);
		return theState;
	}

	@Override
	public State releaseAtomicLock(State state) {
		return this.setVariable(state, 0, 0, modelFactory.processValue(-1));
	}

	/**
	 * Procedure:
	 * 
	 * <ol>
	 * <li>get the current dynamic scope ds0 of the process. Let ss0 be the
	 * static scope associated to ds0.</li>
	 * <li>Let ss1 be the static scope of the new location to move to.</li>
	 * <li>Compute the join (youngest common ancestor) of ss0 and ss1. Also save
	 * the sequence of static scopes from join to ss1.</li>
	 * <li>Iterate UP over dynamic scopes from ds0 up (using parent field) to
	 * the first dynamic scope whose static scope is join.</li>
	 * <li>Iterate DOWN from join to ss1, creating NEW dynamic scopes along the
	 * way.</li>
	 * <li>Set the frame pointer to the new dynamic scope corresponding to ss1,
	 * and set the location to the given location.</li>
	 * <li>Remove all unreachable scopes.</li>
	 * </ol>
	 * 
	 * @param state
	 * @param pid
	 * @param location
	 * @return
	 */
	@Override
	public ImmutableState setLocation(State state, int pid, Location location) {
		ImmutableState theState = (ImmutableState) state;
		ImmutableProcessState[] processArray = theState.copyProcessStates();
		int dynamicScopeId = theState.getProcessState(pid).getDyscopeId();
		ImmutableDynamicScope dynamicScope = theState.getScope(dynamicScopeId);
		Scope ss0 = dynamicScope.lexicalScope();
		Scope ss1 = location.scope();

		if (ss0 == ss1) {
			processArray[pid] = theState.getProcessState(pid).replaceTop(
					stackEntry(location, dynamicScopeId));
			return theState.setProcessStates(processArray);
		} else {
			Scope[] joinSequence = joinSequence(ss0, ss1);
			Scope join = joinSequence[0];

			// iterate UP...
			while (dynamicScope.lexicalScope() != join) {
				dynamicScopeId = theState.getParentId(dynamicScopeId);
				if (dynamicScopeId < 0)
					throw new RuntimeException("State is inconsistent");
				dynamicScope = theState.getScope(dynamicScopeId);
			}
			if (joinSequence.length == 1) {
				processArray[pid] = theState.getProcessState(pid).replaceTop(
						stackEntry(location, dynamicScopeId));
				theState = theState.setProcessStates(processArray);
			} else {
				// iterate DOWN, adding new dynamic scopes...
				int oldNumScopes = theState.numScopes();
				int newNumScopes = oldNumScopes + joinSequence.length - 1;
				int index = 0;
				ImmutableDynamicScope[] newScopes = new ImmutableDynamicScope[newNumScopes];
				ImmutableProcessState process = processArray[pid];

				for (; index < oldNumScopes; index++)
					newScopes[index] = theState.getScope(index);
				for (int i = 1; i < joinSequence.length; i++) {
					// only this process can reach the new dyscope
					BitSet reachers = new BitSet(processArray.length);

					reachers.set(pid);
					newScopes[index] = initialDynamicScope(joinSequence[i],
							dynamicScopeId, index, reachers);
					dynamicScopeId = index;
					index++;
				}
				process = process.replaceTop(stackEntry(location,
						dynamicScopeId));
				setReachablesForProc(newScopes, process);
				processArray[pid] = process;
				theState = new ImmutableState(processArray, newScopes,
						theState.getPathCondition());
			}
			return theState;
		}
	}

	@Override
	public State setProcessState(State state, ProcessState p, int pid) {
		ImmutableState theState = (ImmutableState) state;
		ImmutableProcessState[] newProcesses;

		newProcesses = theState.copyProcessStates();
		newProcesses[pid] = (ImmutableProcessState) p;
		theState = theState.setProcessStates(newProcesses);
		return new ImmutableState(newProcesses, theState.copyScopes(),
				theState.getPathCondition());
	}

	@Override
	public ImmutableState setVariable(State state, int vid, int scopeId,
			SymbolicExpression value) {
		ImmutableState theState = (ImmutableState) state;
		ImmutableDynamicScope oldScope = (ImmutableDynamicScope) theState
				.getScope(scopeId);
		ImmutableDynamicScope[] newScopes = theState.copyScopes();
		SymbolicExpression[] newValues = oldScope.copyValues();
		ImmutableDynamicScope newScope;

		newValues[vid] = value;
		newScope = new ImmutableDynamicScope(oldScope.lexicalScope(),
				oldScope.getParent(), newValues, oldScope.getReachers());
		newScopes[scopeId] = newScope;
		theState = theState.setScopes(newScopes);
		return theState;
	}

	@Override
	public ImmutableState setVariable(State state, Variable variable, int pid,
			SymbolicExpression value) {
		int scopeId = state.getScopeId(pid, variable);

		return setVariable(state, variable.vid(), scopeId, value);
	}

	@Override
	public SymbolicUniverse symbolicUniverse() {
		return universe;
	}

	@Override
	public ImmutableState simplify(State state) {
		ImmutableState theState = flyweight(state);
		ImmutableState result = theState.simplifiedState;

		if (result == null) {
			result = simplifyWork(theState);
			result = flyweight(result);
			theState.simplifiedState = result;
		}
		return result;
	}

	/* ************************ Other public methods *********************** */

	public GMCConfiguration getConfiguration() {
		return config;
	}

	@Override
	public void setEvaluator(Evaluator evaluator) {
		this.evaluator = evaluator;
	}

}
