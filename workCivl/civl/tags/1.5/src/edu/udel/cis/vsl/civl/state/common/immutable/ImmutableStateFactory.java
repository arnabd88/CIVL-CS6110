package edu.udel.cis.vsl.civl.state.common.immutable;

import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.simplifyO;

import java.util.Arrays;
import java.util.BitSet;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.Certainty;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLTypeFactory;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.ModelConfiguration;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ContractClauseExpression.ContractKind;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.state.IF.CIVLHeapException;
import edu.udel.cis.vsl.civl.state.IF.CIVLHeapException.HeapErrorKind;
import edu.udel.cis.vsl.civl.state.IF.CIVLStateException;
import edu.udel.cis.vsl.civl.state.IF.DynamicScope;
import edu.udel.cis.vsl.civl.state.IF.MemoryUnitFactory;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.StackEntry;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.gmc.GMCConfiguration;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SARLException;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.UnaryOperator;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject.SymbolicObjectKind;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicCollection;

/**
 * An implementation of StateFactory based on the Immutable Pattern.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * @author Timothy J. McClory (tmcclory)
 * @author Stephen F. Siegel (siegel)
 * 
 */
public class ImmutableStateFactory implements StateFactory {

	/* ************************** Instance Fields ************************** */

	/**
	 * True iff each canonic state is to be simplified using its path condition.
	 */
	private boolean simplify;

	/**
	 * The number of instances of states that have been created.
	 */
	private long initialNumStateInstances = ImmutableState.instanceCount;

	/**
	 * The model factory.
	 */
	private ModelFactory modelFactory;

	private CIVLTypeFactory typeFactory;

	/**
	 * The map of canonic process states. The key and the corresponding value
	 * should be the same, in order to allow fast checking of existence and
	 * returning the value.
	 */
	private Map<ImmutableProcessState, ImmutableProcessState> processMap = new HashMap<>(
			100000);

	/**
	 * The map of canonic dyscopes. The key and the corresponding value should
	 * be the same, in order to allow fast checking of existence and returning
	 * the value.
	 */
	private Map<ImmutableDynamicScope, ImmutableDynamicScope> scopeMap = new HashMap<>(
			100000);

	/**
	 * The number of canonic states.
	 */
	private int stateCount = 0;

	/**
	 * The number of canonic process states.
	 */
	private int processCount = 0;

	/**
	 * The number of canonic dyscopes.
	 */
	private int dyscopeCount = 0;

	/**
	 * The map of canonic states. The key and the corresponding value should be
	 * the same, in order to allow fast checking of existence and returning the
	 * value.
	 */
	private Map<ImmutableState, ImmutableState> stateMap = new HashMap<>(
			1000000);

	private SymbolicExpression undefinedProcessValue;

	/**
	 * the CIVL configuration specified by the comamnd line
	 */
	private CIVLConfiguration config;

	/**
	 * Class used to wrap integer arrays so they can be used as keys in hash
	 * maps. This is used to map dyscope ID substitution maps to SARL
	 * substituters, in order to reuse substituters when the same substitution
	 * map comes up again and again. Since the substituters cache their results,
	 * this has the potential to increase performance.
	 * 
	 * @author siegel
	 *
	 */
	private class IntArray {
		private int[] contents;

		public IntArray(int[] contents) {
			this.contents = contents;
		}

		@Override
		public boolean equals(Object obj) {
			if (obj instanceof IntArray) {
				return Arrays.equals(contents, ((IntArray) obj).contents);
			}
			return false;
		}

		@Override
		public int hashCode() {
			return Arrays.hashCode(contents);
		}
	}

	private Map<IntArray, UnaryOperator<SymbolicExpression>> dyscopeSubMap = new HashMap<>();

	/**
	 * The reasoner for evaluating boolean formulas, provided by SARL.
	 */
	private Reasoner trueReasoner;

	/**
	 * The symbolic universe, provided by SARL.
	 */
	private SymbolicUniverse universe;

	private SymbolicUtility symbolicUtil;

	private ImmutableMemoryUnitFactory memUnitFactory;

	private ReservedConstant isReservedSymbolicConstant;

	private List<Variable> inputVariables;

	private Set<HeapErrorKind> emptyHeapErrorSet = new HashSet<>(0);

	/* **************************** Constructors *************************** */

	/**
	 * Factory to create all state objects.
	 */
	public ImmutableStateFactory(ModelFactory modelFactory,
			SymbolicUtility symbolicUtil, MemoryUnitFactory memFactory,
			GMCConfiguration gmcConfig, CIVLConfiguration config) {
		this.modelFactory = modelFactory;
		this.inputVariables = modelFactory.inputVariables();
		this.typeFactory = modelFactory.typeFactory();
		this.symbolicUtil = symbolicUtil;
		this.universe = modelFactory.universe();
		this.trueReasoner = universe.reasoner(universe.trueExpression());
		this.simplify = gmcConfig.getAnonymousSection().isTrue(simplifyO);
		this.memUnitFactory = (ImmutableMemoryUnitFactory) memFactory;
		this.undefinedProcessValue = modelFactory.undefinedValue(typeFactory
				.processSymbolicType());
		isReservedSymbolicConstant = new ReservedConstant();
		this.config = config;
	}

	/* ********************** Methods from StateFactory ******************** */

	@Override
	public ImmutableState addProcess(State state, CIVLFunction function,
			SymbolicExpression[] arguments, int callerPid) {
		ImmutableState theState = createNewProcess(state);

		return pushCallStack2(theState, state.numProcs(), function, -1,
				arguments, callerPid);
	}

	@Override
	public State addProcess(State state, CIVLFunction function,
			int functionParentDyscope, SymbolicExpression[] arguments,
			int callerPid) {
		ImmutableState theState = createNewProcess(state);

		return pushCallStack2(theState, state.numProcs(), function,
				functionParentDyscope, arguments, callerPid);
	}

	/**
	 * <p>
	 * In this implementation of canonic: process states are collected, heaps
	 * are collected, dynamic scopes are collected, the flyweight representative
	 * is taken, simplify is called if that option is selected, then the
	 * flyweight representative is taken again.
	 * </p>
	 * 
	 * 
	 * @throws CIVLStateException
	 */
	@Override
	public ImmutableState canonic(State state, boolean collectProcesses,
			boolean collectScopes, boolean collectHeaps,
			Set<HeapErrorKind> toBeIgnored) throws CIVLHeapException {
		ImmutableState theState = (ImmutableState) state;

		// performance experiment: seems to make no difference
		// theState = flyweight(theState);
		if (collectProcesses)
			theState = collectProcesses(theState);
		if (collectScopes)
			theState = collectScopes(theState, toBeIgnored);
		if (collectHeaps)
			theState = collectHeaps(theState, toBeIgnored);
		// theState = collectSymbolicConstants(theState, collectHeaps);
		theState = flyweight(theState);
		if (simplify) {
			ImmutableState simplifiedState = theState.simplifiedState;

			if (simplifiedState == null) {
				simplifiedState = simplify(theState);
				// if (theState != simplifiedState)
				// simplifiedState = collectSymbolicConstants(simplifiedState,
				// collectHeaps);
				simplifiedState = flyweight(simplifiedState);
				theState.simplifiedState = simplifiedState;
				simplifiedState.simplifiedState = simplifiedState;
			}
			return simplifiedState;
		}
		return theState;
	}

	@Override
	public ImmutableState collectHeaps(State state,
			Set<HeapErrorKind> toBeIgnored) throws CIVLHeapException {
		ImmutableState theState = (ImmutableState) state;

		// only collect heaps when necessary.
		if (!this.hasNonEmptyHeaps(theState))
			return theState;
		else {
			Set<SymbolicExpression> reachable = this
					.reachableHeapObjectsOfState(theState);
			int numDyscopes = theState.numDyscopes();
			int numHeapFields = typeFactory.heapType().getNumMallocs();
			Map<SymbolicExpression, SymbolicExpression> oldToNewHeapMemUnits = new HashMap<>();
			ImmutableDynamicScope[] newScopes = new ImmutableDynamicScope[numDyscopes];
			ReferenceExpression[] fieldRefs = new ReferenceExpression[numHeapFields];

			for (int mallocId = 0; mallocId < numHeapFields; mallocId++) {
				fieldRefs[mallocId] = universe.tupleComponentReference(
						universe.identityReference(),
						universe.intObject(mallocId));
			}
			for (int dyscopeId = 0; dyscopeId < numDyscopes; dyscopeId++) {
				DynamicScope dyscope = theState.getDyscope(dyscopeId);
				SymbolicExpression heap = dyscope.getValue(0);

				if (heap.isNull())
					continue;
				else {
					SymbolicExpression newHeap = heap;
					SymbolicExpression heapPointer = this.symbolicUtil
							.makePointer(dyscopeId, 0,
									universe.identityReference());

					for (int mallocId = 0; mallocId < numHeapFields; mallocId++) {
						SymbolicExpression heapField = universe.tupleRead(heap,
								universe.intObject(mallocId));
						int length = this.symbolicUtil.extractInt(null,
								(NumericExpression) universe.length(heapField));
						Map<Integer, Integer> oldID2NewID = new HashMap<>();
						int numRemoved = 0;
						SymbolicExpression newHeapField = heapField;
						boolean hasNew = false;

						for (int objectId = 0; objectId < length; objectId++) {
							ReferenceExpression objectRef = universe
									.arrayElementReference(fieldRefs[mallocId],
											universe.integer(objectId));
							SymbolicExpression objectPtr = this.symbolicUtil
									.setSymRef(heapPointer, objectRef);

							if (!reachable.contains(objectPtr)) {
								SymbolicExpression heapObj = universe
										.arrayRead(heapField,
												universe.integer(objectId));

								if (config.checkMemoryLeak()
										&& !symbolicUtil
												.isInvalidHeapObject(heapObj)
										&& !toBeIgnored
												.contains(HeapErrorKind.UNREACHABLE)) {
									throw new CIVLHeapException(
											ErrorKind.MEMORY_LEAK,
											Certainty.CONCRETE, theState,
											dyscope.name(), dyscopeId, heap,
											mallocId, objectId,
											HeapErrorKind.UNREACHABLE, dyscope
													.lexicalScope().getSource());
								}
								// remove unreachable heap object
								// updates references
								for (int nextId = objectId + 1; nextId < length; nextId++) {
									if (oldID2NewID.containsKey(nextId))
										oldID2NewID.put(nextId,
												oldID2NewID.get(nextId) - 1);
									else
										oldID2NewID.put(nextId, nextId - 1);
								}
								// remove object
								hasNew = true;
								newHeapField = universe.removeElementAt(
										newHeapField, objectId - numRemoved);
								numRemoved++;
							}
						}
						if (oldID2NewID.size() > 0)
							addOldToNewHeapMemUnits(oldID2NewID, heapPointer,
									fieldRefs[mallocId], oldToNewHeapMemUnits);
						if (hasNew)
							newHeap = universe.tupleWrite(newHeap,
									universe.intObject(mallocId), newHeapField);
					}
					if (symbolicUtil.isEmptyHeap(newHeap))
						newHeap = universe.nullExpression();
					theState = this
							.setVariable(theState, 0, dyscopeId, newHeap);
				}
			}
			computeOldToNewHeapPointers(theState, oldToNewHeapMemUnits,
					oldToNewHeapMemUnits);
			for (int i = 0; i < numDyscopes; i++)
				newScopes[i] = theState.getDyscope(i).updateHeapPointers(
						oldToNewHeapMemUnits, universe);
			theState = theState.setScopes(newScopes);
			return theState;
		}
	}

	@Override
	public ImmutableState collectScopes(State state,
			Set<HeapErrorKind> toBeIgnored) throws CIVLHeapException {
		ImmutableState theState = (ImmutableState) state;
		int oldNumScopes = theState.numDyscopes();
		int[] oldToNew = numberScopes(theState);
		boolean change = false;
		int newNumScopes = 0;

		for (int i = 0; i < oldNumScopes; i++) {
			int id = oldToNew[i];

			if (id >= 0)
				newNumScopes++;
			if (!change && id != i)
				change = true;
			if (id < 0 && config.checkMemoryLeak()
					&& !toBeIgnored.contains(HeapErrorKind.NONEMPTY)) {
				ImmutableDynamicScope scopeToBeRemoved = theState.getDyscope(i);
				Variable heapVariable = scopeToBeRemoved.lexicalScope()
						.variable(ModelConfiguration.HEAP_VAR);
				SymbolicExpression heapValue = scopeToBeRemoved
						.getValue(heapVariable.vid());

				if (!(heapValue.isNull() || symbolicUtil.isEmptyHeap(heapValue))) {
					throw new CIVLHeapException(ErrorKind.MEMORY_LEAK,
							Certainty.CONCRETE, state, scopeToBeRemoved.name(),
							i, heapValue, HeapErrorKind.NONEMPTY,
							heapVariable.getSource());
				}
			}
		}
		if (change) {
			IntArray key = new IntArray(oldToNew);
			UnaryOperator<SymbolicExpression> substituter = dyscopeSubMap
					.get(key);

			if (substituter == null) {
				substituter = universe.mapSubstituter(scopeSubMap(oldToNew));
				dyscopeSubMap.put(key, substituter);
			}

			ImmutableDynamicScope[] newScopes = new ImmutableDynamicScope[newNumScopes];
			int numProcs = theState.numProcs();
			ImmutableProcessState[] newProcesses = new ImmutableProcessState[numProcs];
			BooleanExpression newPathCondition = (BooleanExpression) substituter
					.apply(theState.getPathCondition());

			for (int i = 0; i < oldNumScopes; i++) {
				int newId = oldToNew[i];

				if (newId >= 0) {
					ImmutableDynamicScope oldScope = theState.getDyscope(i);
					int oldParent = oldScope.getParent();
					int oldParentIdentifier = oldScope.identifier();

					newScopes[newId] = oldScope.updateDyscopeIds(substituter,
							universe, oldParent < 0 ? oldParent
									: oldToNew[oldParent], oldParentIdentifier);
				}
			}
			for (int pid = 0; pid < numProcs; pid++)
				newProcesses[pid] = theState.getProcessState(pid)
						.updateDyscopes(oldToNew);
			theState = ImmutableState.newState(theState, newProcesses,
					newScopes, newPathCondition);
		}
		if (theState.numDyscopes() == 1
				&& !toBeIgnored.contains(HeapErrorKind.NONEMPTY)
				&& theState.getProcessState(0).hasEmptyStack()) {
			// checks the memory leak for the final state
			DynamicScope dyscope = state.getDyscope(0);
			SymbolicExpression heap = dyscope.getValue(0);

			if (config.checkMemoryLeak() && !symbolicUtil.isEmptyHeap(heap))
				throw new CIVLHeapException(ErrorKind.MEMORY_LEAK,
						Certainty.CONCRETE, state, "d0", 0, heap,
						HeapErrorKind.NONEMPTY, dyscope.lexicalScope()
								.getSource());

		}
		return theState;
	}

	@Override
	public State getAtomicLock(State state, int pid) {
		Variable atomicVar = modelFactory.atomicLockVariableExpression()
				.variable();

		// assert state.getVariableValue(0, atomicVar.vid())
		return this.setVariable(state, atomicVar.vid(), 0,
				modelFactory.processValue(pid));
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
	public ImmutableState initialState(Model model) throws CIVLHeapException {
		// HashMap<Integer, Map<SymbolicExpression, Boolean>> reachableMUs = new
		// HashMap<Integer, Map<SymbolicExpression, Boolean>>();
		// HashMap<Integer, Map<SymbolicExpression, Boolean>> reachableMUwtPtr =
		// new HashMap<Integer, Map<SymbolicExpression, Boolean>>();
		ImmutableState state;
		CIVLFunction function = model.system();
		int numArgs = function.parameters().size();
		SymbolicExpression[] arguments = new SymbolicExpression[numArgs];
		Variable atomicVar = modelFactory.atomicLockVariableExpression()
				.variable();
		Variable timeCountVar = modelFactory.timeCountVariable();

		// reachableMUs.put(0, new HashMap<SymbolicExpression, Boolean>());
		state = new ImmutableState(new ImmutableProcessState[0],
				new ImmutableDynamicScope[0], universe.trueExpression());
		// system function doesn't have any argument, because the General
		// transformer has translated away all parameters of the main function.
		state = addProcess(state, function, arguments, -1);
		state = this.setVariable(state, atomicVar.vid(), 0,
				undefinedProcessValue);
		if (timeCountVar != null)
			state = this.setVariable(state, timeCountVar.vid(), 0,
					universe.zeroInt());
		// state = this.computeReachableMemUnits(state, 0);
		return canonic(state, false, false, false, emptyHeapErrorSet);
	}

	@Override
	public boolean isDescendantOf(State state, int ancestor, int descendant) {
		if (ancestor == descendant) {
			return false;
		} else {
			int parent = state.getParentId(descendant);

			while (parent >= 0) {
				if (ancestor == parent)
					return true;
				parent = state.getParentId(parent);
			}
		}
		return false;
	}

	@Override
	public boolean lockedByAtomic(State state) {
		SymbolicExpression symbolicAtomicPid = state.getVariableValue(0,
				modelFactory.atomicLockVariableExpression().variable().vid());
		int atomicPid = modelFactory.getProcessId(modelFactory.systemSource(),
				symbolicAtomicPid);

		return atomicPid >= 0;
	}

	@Override
	// TODO: improve the performance: keep track of depth of dyscopes
	public int lowestCommonAncestor(State state, int one, int another) {
		if (one == another) {
			return one;
		} else {
			int parent = one;

			while (parent >= 0) {
				if (parent == another
						|| this.isDescendantOf(state, parent, another))
					return parent;
				parent = state.getParentId(parent);
			}
		}
		return state.rootDyscopeID();
	}

	@Override
	public ImmutableState popCallStack(State state, int pid) {
		ImmutableState theState = (ImmutableState) state;
		ImmutableProcessState process = theState.getProcessState(pid);
		ImmutableProcessState[] processArray = theState.copyProcessStates();
		ImmutableDynamicScope[] newScopes = theState.copyScopes();
		// DynamicScope dyscopeExpired =
		// state.getDyscope(process.getDyscopeId());
		// Scope staticScope = dyscopeExpired.lexicalScope();
		// Map<Integer, Map<SymbolicExpression, Boolean>> reachableMUwoPtr =
		// null, reachableMUwtPtr = null;

		processArray[pid] = process.pop();
		setReachablesForProc(newScopes, processArray[pid]);
		// if (!processArray[pid].hasEmptyStack() && staticScope.hasVariable())
		// {
		// reachableMUwoPtr = this.setReachableMemUnits(theState, pid, this
		// .removeReachableMUwoPtrFromDyscopes(new HashSet<Integer>(
		// Arrays.asList(process.getDyscopeId())), theState,
		// pid), false);
		// if (staticScope.hasVariableWtPointer())
		// reachableMUwtPtr = this.setReachableMemUnits(theState, pid,
		// this.computeReachableMUofProc(theState, pid, true),
		// true);
		// }
		theState = ImmutableState.newState(theState, processArray, newScopes,
				null);
		return theState;
	}

	@Override
	public int processInAtomic(State state) {
		// TODO use a field for vid
		SymbolicExpression symbolicAtomicPid = state.getVariableValue(0,
				modelFactory.atomicLockVariableExpression().variable().vid());

		return modelFactory.getProcessId(modelFactory.systemSource(),
				symbolicAtomicPid);
	}

	@Override
	public ImmutableState pushCallStack(State state, int pid,
			CIVLFunction function, SymbolicExpression[] arguments) {
		return pushCallStack2((ImmutableState) state, pid, function, -1,
				arguments, pid);
	}

	@Override
	public State pushCallStack(State state, int pid, CIVLFunction function,
			int functionParentDyscope, SymbolicExpression[] arguments) {
		return pushCallStack2((ImmutableState) state, pid, function,
				functionParentDyscope, arguments, pid);
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
			// Map<Integer, Map<SymbolicExpression, Boolean>>
			// reachableMUsWtPointer, reachableMUsWoPointer;

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
			// newReachableMemUnitsMap =
			// updateProcessReferencesInReachableMemoryUnitsMap(
			// theState, oldToNewPidMap);
			// reachableMUsWtPointer = this.updatePIDsForReachableMUs(
			// oldToNewPidMap, theState, true);
			// reachableMUsWoPointer = this.updatePIDsForReachableMUs(
			// oldToNewPidMap, theState, false);
			newScopes = updateProcessReferencesInScopes(theState,
					oldToNewPidMap);
			theState = ImmutableState.newState(theState, newProcesses,
					newScopes, null);
		}
		return theState;
	}

	@Override
	public State terminateProcess(State state, int pid) {
		ImmutableState theState = (ImmutableState) state;
		ImmutableProcessState emptyProcessState = new ImmutableProcessState(
				pid, state.getProcessState(pid).identifier());

		return theState.setProcessState(pid, emptyProcessState);
	}

	@Override
	public ImmutableState removeProcess(State state, int pid) {
		ImmutableState theState = (ImmutableState) state;

		theState = theState.setProcessState(pid, null);
		return theState;
	}

	@Override
	public State releaseAtomicLock(State state) {
		Variable atomicVar = modelFactory.atomicLockVariableExpression()
				.variable();

		return this.setVariable(state, atomicVar.vid(), 0,
				modelFactory.processValue(-1));
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
	// TODO UPDATE reachable mem units
	public ImmutableState setLocation(State state, int pid, Location location,
			boolean accessChanged) {
		ImmutableState theState = (ImmutableState) state;
		ImmutableProcessState[] processArray = theState.copyProcessStates();
		int dynamicScopeId = theState.getProcessState(pid).getDyscopeId();
		ImmutableDynamicScope dynamicScope = theState
				.getDyscope(dynamicScopeId);
		int dynamicScopeIdentifier = dynamicScope.identifier();
		Scope ss0 = dynamicScope.lexicalScope();
		Scope ss1 = location.scope();

		if (ss0 == ss1) {// remains in the same dyscope
			processArray[pid] = theState.getProcessState(pid)
					.replaceTop(
							stackEntry(location, dynamicScopeId,
									dynamicScopeIdentifier));
			theState = theState.setProcessStates(processArray);
			// if (accessChanged)
			// theState = updateReachableMemUnitsAccess(theState, pid);
			return theState;
		} else {// a different dyscope is encountered
			Scope[] joinSequence = joinSequence(ss0, ss1);
			Scope join = joinSequence[0];
			Set<Integer> dyscopeIDsequence = new HashSet<>();

			// iterate UP...
			while (dynamicScope.lexicalScope() != join) {
				dyscopeIDsequence.add(dynamicScopeId);
				dynamicScopeId = theState.getParentId(dynamicScopeId);
				if (dynamicScopeId < 0)
					throw new RuntimeException("State is inconsistent");
				dynamicScope = theState.getDyscope(dynamicScopeId);
				dynamicScopeIdentifier = dynamicScope.identifier();
			}
			if (joinSequence.length == 1) {
				// Map<Integer, Map<SymbolicExpression, Boolean>>
				// reachableMUwoPtr, reachableMUwtPtr;

				// the previous scope(s) just disappear
				processArray[pid] = theState.getProcessState(pid).replaceTop(
						stackEntry(location, dynamicScopeId,
								dynamicScopeIdentifier));
				// reachableMUwoPtr = this.setReachableMemUnits(theState, pid,
				// this.removeReachableMUwoPtrFromDyscopes(
				// dyscopeIDsequence, theState, pid), false);
				// reachableMUwtPtr = this.setReachableMemUnits(theState, pid,
				// this.computeReachableMUofProc(theState, pid, true),
				// true);
				theState = ImmutableState.newState(theState, processArray,
						null, null);
			} else {
				// iterate DOWN, adding new dynamic scopes...
				int oldNumScopes = theState.numDyscopes();
				int newNumScopes = oldNumScopes + joinSequence.length - 1;
				int index = 0;
				ImmutableDynamicScope[] newScopes = new ImmutableDynamicScope[newNumScopes];
				int[] newDyscopes = new int[joinSequence.length - 1];

				for (; index < oldNumScopes; index++)
					newScopes[index] = theState.getDyscope(index);
				for (int i = 1; i < joinSequence.length; i++) {
					// only this process can reach the new dyscope
					BitSet reachers = new BitSet(processArray.length);

					reachers.set(pid);
					newScopes[index] = initialDynamicScope(joinSequence[i],
							dynamicScopeId, dynamicScopeIdentifier, index,
							reachers);
					dynamicScopeId = index;
					newDyscopes[i - 1] = dynamicScopeId;
					index++;
				}
				processArray[pid] = processArray[pid].replaceTop(stackEntry(
						location, dynamicScopeId,
						newScopes[dynamicScopeId].identifier()));
				setReachablesForProc(newScopes, processArray[pid]);
				theState = ImmutableState.newState(theState, processArray,
						newScopes, null);
				// theState = addReachableMemUnitsFromDyscope(newDyscopes,
				// newScopes, theState, pid);
			}
			// if (accessChanged)
			// theState = updateReachableMemUnitsAccess(theState, pid);
			return theState;
		}
	}

	@Override
	public State setProcessState(State state, ProcessState p) {
		ImmutableState theState = (ImmutableState) state;
		ImmutableState newState;
		ImmutableProcessState[] newProcesses;
		int pid = p.getPid();

		newProcesses = theState.copyProcessStates();
		newProcesses[pid] = (ImmutableProcessState) p;
		theState = theState.setProcessStates(newProcesses);
		newState = new ImmutableState(newProcesses, theState.copyScopes(),
				theState.getPathCondition());
		newState = newState.setSnapshotsQueues(theState.getSnapshotsQueues());
		return newState;
	}

	@Override
	public ImmutableState setVariable(State state, int vid, int scopeId,
			SymbolicExpression value) {
		ImmutableState theState = (ImmutableState) state;
		ImmutableDynamicScope oldScope = (ImmutableDynamicScope) theState
				.getDyscope(scopeId);
		ImmutableDynamicScope[] newScopes = theState.copyScopes();
		SymbolicExpression[] newValues = oldScope.copyValues();
		ImmutableDynamicScope newScope;

		newValues[vid] = value;
		newScope = new ImmutableDynamicScope(oldScope.lexicalScope(),
				oldScope.getParent(), 0,// TODO oldScope.getParentIdentifier()
				newValues, oldScope.getReachers(), oldScope.identifier());
		newScopes[scopeId] = newScope;
		theState = theState.setScopes(newScopes);
		return theState;
	}

	@Override
	public ImmutableState setVariable(State state, Variable variable, int pid,
			SymbolicExpression value) {
		int scopeId = state.getDyscopeID(pid, variable);

		return setVariable(state, variable.vid(), scopeId, value);
	}

	@Override
	public ImmutableState simplify(State state) {
		ImmutableState theState = (ImmutableState) state;

		if (theState.simplifiedState != null)
			return theState.simplifiedState;

		int numScopes = theState.numDyscopes();
		BooleanExpression pathCondition = theState.getPathCondition();
		ImmutableDynamicScope[] newDynamicScopes = null;
		Reasoner reasoner = universe.reasoner(pathCondition);
		BooleanExpression newPathCondition;

		for (int i = 0; i < numScopes; i++) {
			ImmutableDynamicScope oldScope = theState.getDyscope(i);
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
					newDynamicScopes[i2] = theState.getDyscope(i2);
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
		// if (enableMpiContract) {
		// Map<Integer, ArrayList<ImmutableCollectiveSnapshotsEntry>> newMap =
		// new HashMap<>();
		// Map<Integer, ArrayList<ImmutableCollectiveSnapshotsEntry>> oldMap =
		// theState
		// .getSnapshotsQueues();
		// Iterator<Integer> keyIter = oldMap.keySet().iterator();
		//
		// while (keyIter.hasNext()) {
		// int key = keyIter.next();
		// ArrayList<ImmutableCollectiveSnapshotsEntry> queue = oldMap
		// .get(key);
		//
		// if (queue != null) {
		// for (int i = 0; i < queue.size(); i++) {
		// ImmutableCollectiveSnapshotsEntry entry = queue.get(i);
		//
		// entry = (ImmutableCollectiveSnapshotsEntry) entry
		// .simplify();
		// queue.set(i, entry);
		// }
		// }
		// newMap.put(key, queue);
		// }
		// theState = theState.setSnapshotsQueues(newMap);
		// }
		return theState;
	}

	@Override
	public SymbolicUniverse symbolicUniverse() {
		return universe;
	}

	@Override
	public Pair<State, SymbolicExpression> malloc(State state, int dyscopeId,
			int mallocId, SymbolicExpression heapObject) {
		DynamicScope dyscope = state.getDyscope(dyscopeId);
		IntObject indexObj = universe.intObject(mallocId);
		SymbolicExpression heapValue = dyscope.getValue(0);
		SymbolicExpression heapField;
		SymbolicExpression heapAtomicObjectPtr;
		ReferenceExpression symRef;
		NumericExpression heapLength;

		if (heapValue.isNull())
			heapValue = typeFactory.heapType().getInitialValue();
		heapField = universe.tupleRead(heapValue, indexObj);
		heapLength = universe.length(heapField);
		heapField = universe.append(heapField, heapObject);
		heapValue = universe.tupleWrite(heapValue, indexObj, heapField);
		state = setVariable(state, 0, dyscopeId, heapValue);
		symRef = (ReferenceExpression) universe.canonic(universe
				.identityReference());
		symRef = universe.tupleComponentReference(symRef, indexObj);
		symRef = universe.arrayElementReference(symRef, heapLength);
		symRef = universe.arrayElementReference(symRef, universe.zeroInt());
		heapAtomicObjectPtr = symbolicUtil.makePointer(dyscopeId, 0, symRef);
		return new Pair<>(state, heapAtomicObjectPtr);
	}

	@Override
	public Pair<State, SymbolicExpression> malloc(State state, int pid,
			int dyscopeId, int mallocId, SymbolicType elementType,
			NumericExpression elementCount) {
		DynamicScope dyscope = state.getDyscope(dyscopeId);
		SymbolicExpression heapValue = dyscope.getValue(0).isNull() ? typeFactory
				.heapType().getInitialValue() : dyscope.getValue(0);
		IntObject index = universe.intObject(mallocId);
		SymbolicExpression heapField = universe.tupleRead(heapValue, index);
		int length = ((IntegerNumber) universe.extractNumber(universe
				.length(heapField))).intValue();
		StringObject heapObjectName = universe.stringObject("Hop" + pid + "s"
				+ dyscopeId + "f" + mallocId + "o" + length);
		SymbolicType heapObjectType = universe.arrayType(elementType,
				elementCount);
		SymbolicExpression heapObject = universe.symbolicConstant(
				heapObjectName, heapObjectType);

		return this.malloc(state, dyscopeId, mallocId, heapObject);
	}

	@Override
	public State deallocate(State state, SymbolicExpression heapObjectPointer,
			int dyscopeId, int mallocId, int index) {
		SymbolicExpression heapValue = state.getDyscope(dyscopeId).getValue(0);
		IntObject mallocIndex = universe.intObject(mallocId);
		SymbolicExpression heapField = universe.tupleRead(heapValue,
				mallocIndex);
		// int heapFieldLength = ((IntegerNumber)
		// universe.extractNumber(universe
		// .length(heapField))).intValue();
		// Map<SymbolicExpression, SymbolicExpression> oldToNewHeapMemUnits =
		// new HashMap<>(
		// heapFieldLength - index);
		// Map<SymbolicExpression, SymbolicExpression> oldToNewHeapPointers =
		// new HashMap<>();
		// int numDyscopes = state.numDyscopes();
		// ImmutableDynamicScope[] newScopes = new
		// ImmutableDynamicScope[numDyscopes];
		ImmutableState theState = (ImmutableState) state;

		// oldToNewHeapMemUnits.put(symbolicUtil.heapMemUnit(heapObjectPointer),
		// this.symbolicUtil.undefinedPointer());
		heapField = universe.arrayWrite(heapField, universe.integer(index),
				symbolicUtil.invalidHeapObject(((SymbolicArrayType) heapField
						.type()).elementType()));
		heapValue = universe.tupleWrite(heapValue, mallocIndex, heapField);
		theState = this.setVariable(theState, 0, dyscopeId, heapValue);
		// computes all affected pointers' oldToNew map
		// this.computeOldToNewHeapPointers(theState, oldToNewHeapMemUnits,
		// oldToNewHeapPointers);
		// for (int i = 0; i < numDyscopes; i++)
		// newScopes[i] = theState.getDyscope(i).updateHeapPointers(
		// oldToNewHeapPointers, universe);
		// theState = theState.setScopes(newScopes);
		return theState;
	}

	/* *************************** Private Methods ************************* */

	/**
	 * Adds a new initial process state to the given state.
	 * 
	 * @param state
	 *            The old state.
	 * @return A new instance of state with only the process states changed.
	 */
	private ImmutableState createNewProcess(State state) {
		ImmutableState theState = (ImmutableState) state;
		int numProcs = theState.numProcs();
		ImmutableProcessState[] newProcesses;

		newProcesses = theState.copyAndExpandProcesses();
		newProcesses[numProcs] = new ImmutableProcessState(numProcs,
				this.processCount++);
		theState = theState.setProcessStates(newProcesses);
		return theState;
	}

	/**
	 * Returns the canonicalized version of the given state.
	 * 
	 * @param state
	 *            the old state
	 * @return the state equivalent to the given state and which is
	 *         canonicalized.
	 */
	private ImmutableState flyweight(State state) {
		ImmutableState theState = (ImmutableState) state;

		if (theState.isCanonic())
			return theState;
		else {
			ImmutableState result = stateMap.get(theState);

			if (result == null) {
				result = theState;
				// result = reachableMemoryAnalysis(theState);
				result.makeCanonic(stateCount, universe, scopeMap, processMap);
				stateCount++;
				stateMap.put(result, result);
			}
			return result;
		}
	}

	/**
	 * Creates a dyscope in its initial state.
	 * 
	 * @param lexicalScope
	 *            The lexical scope corresponding to this dyscope.
	 * @param parent
	 *            The parent of this dyscope. -1 only for the topmost dyscope.
	 * @return A new dynamic scope.
	 */
	private ImmutableDynamicScope initialDynamicScope(Scope lexicalScope,
			int parent, int parentIdentifier, int dynamicScopeId,
			BitSet reachers) {
		return new ImmutableDynamicScope(lexicalScope, parent,
				parentIdentifier, initialValues(lexicalScope), reachers,
				this.dyscopeCount++);
	}

	/**
	 * Creates the initial value of a given lexical scope.
	 * 
	 * @param lexicalScope
	 *            The lexical scope whose variables are to be initialized.
	 * @return An array of initial values of variables of the given lexical
	 *         scope.
	 */
	private SymbolicExpression[] initialValues(Scope lexicalScope) {
		// TODO: special handling for input variables in root scope?
		SymbolicExpression[] values = new SymbolicExpression[lexicalScope
				.variables().size()];

		for (int i = 0; i < values.length; i++) {
			values[i] = universe.nullExpression();
		}
		return values;
	}

	// /**
	// * Checks if a heap is null or empty.
	// *
	// * @param heapValue
	// * The value of the heap to be checked.
	// * @return True iff the heap has null value or is empty.
	// */
	// private boolean isEmptyHeap(SymbolicExpression heapValue) {
	// if (heapValue.isNull())
	// return true;
	// else {
	// SymbolicSequence<?> heapFields = (SymbolicSequence<?>) heapValue
	// .argument(0);
	// int count = heapFields.size();
	//
	// for (int i = 0; i < count; i++) {
	// SymbolicExpression heapField = heapFields.get(i);
	// SymbolicSequence<?> heapFieldObjets = (SymbolicSequence<?>) heapField
	// .argument(0);
	// int size = heapFieldObjets.size();
	//
	// for (int j = 0; j < size; j++) {
	// SymbolicExpression heapFieldObj = heapFieldObjets.get(j);
	// SymbolicObject heapFieldObjValue = heapFieldObj.argument(0);
	//
	// if (heapFieldObjValue.symbolicObjectKind() == SymbolicObjectKind.STRING)
	// {
	// String value = ((StringObject) heapFieldObjValue)
	// .getString();
	//
	// if (value.equals("UNDEFINED"))
	// continue;
	// }
	// return false;
	// }
	// }
	// }
	// return true;
	// }

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
		int numScopes = state.numDyscopes();
		int numProcs = state.numProcs();
		int[] oldToNew = new int[numScopes];
		int nextScopeId = 1;

		// the root dyscope is forced to be 0
		oldToNew[0] = 0;
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

	/**
	 * Checks if a given claim is not satisfiable.
	 * 
	 * @param claim
	 *            The given claim.
	 * @return True iff the given claim is evaluated to be false.
	 */
	private boolean nsat(BooleanExpression claim) {
		return trueReasoner.isValid(universe.not(claim));
	}

	/**
	 * Creates a map of process value's according to PID map from old PID to new
	 * PID.
	 * 
	 * @param oldToNewPidMap
	 *            The map of old PID to new PID, i.e, oldToNewPidMap[old PID] =
	 *            new PID.
	 * @return The map of process value's from old process value to new process
	 *         value.
	 */
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
	 * @param functionParentDyscope
	 *            The dyscope ID of the parent of the new function
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
			CIVLFunction function, int functionParentDyscope,
			SymbolicExpression[] arguments, int callerPid) {
		Scope containingStaticScope = function.containingScope();
		Scope functionStaticScope = function.outerScope();
		ImmutableProcessState[] newProcesses = state.copyProcessStates();
		int numScopes = state.numDyscopes();
		SymbolicExpression[] values;
		ImmutableDynamicScope[] newScopes;
		int sid;
		int containingDynamicScopeId = functionParentDyscope, containingDynamicScopeIdentifier;
		BitSet bitSet = new BitSet(newProcesses.length);

		if (containingDynamicScopeId < 0)
			if (callerPid >= 0) {
				ProcessState caller = state.getProcessState(callerPid);
				ImmutableDynamicScope containingDynamicScope;

				if (caller.stackSize() == 0)
					throw new IllegalArgumentException(
							"Calling process has empty stack: " + callerPid);
				containingDynamicScopeId = caller.getDyscopeId();
				while (containingDynamicScopeId >= 0) {
					containingDynamicScope = (ImmutableDynamicScope) state
							.getDyscope(containingDynamicScopeId);
					if (containingStaticScope == containingDynamicScope
							.lexicalScope())
						break;
					containingDynamicScopeId = state
							.getParentId(containingDynamicScopeId);
				}
				if (containingDynamicScopeId < 0)
					throw new IllegalArgumentException(
							"Called function not visible:\nfunction: "
									+ function + "\npid: " + pid
									+ "\ncallerPid:" + callerPid
									+ "\narguments: "
									+ Arrays.toString(arguments));
			} else {
				containingDynamicScopeId = -1;
			}
		newScopes = state.copyAndExpandScopes();
		sid = numScopes;
		values = initialValues(functionStaticScope);
		for (int i = 0; i < arguments.length; i++)
			if (arguments[i] != null)
				values[i + 1] = arguments[i];
		bitSet.set(pid);
		if (containingDynamicScopeId < 0)
			containingDynamicScopeIdentifier = -1;
		else
			containingDynamicScopeIdentifier = newScopes[containingDynamicScopeId]
					.identifier();
		newScopes[sid] = new ImmutableDynamicScope(functionStaticScope,
				containingDynamicScopeId, containingDynamicScopeIdentifier,
				values, bitSet, this.dyscopeCount++);
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
				stackEntry(null, sid, newScopes[sid].identifier()));
		// newProcesses[pid] = addReachableMemUnitsFromDyscope(sid,
		// newScopes[sid], newProcesses[pid]);
		// state = new ImmutableState(newProcesses, newScopes,
		// state.getPathCondition());
		state = ImmutableState.newState(state, newProcesses, newScopes, null);
		// state = this.addReachableMemUnitsFromDyscope(new int[] { sid },
		// newScopes, state, pid, function.startLocation());
		state = setLocation(state, pid, function.startLocation());
		return state;
	}

	/**
	 * Creates a map of scope value's according to the given dyscope map from
	 * old dyscope ID to new dyscope ID.
	 * 
	 * @param oldToNewSidMap
	 *            The map of old dyscope ID to new dyscoep ID, i.e,
	 *            oldToNewSidMap[old dyscope ID] = new dyscope ID.
	 * @return The map of scope value's from old scope value to new scope value.
	 */
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
	 * @param dyscopeIdentifier
	 *            The identifier of the dynamic scope that the process is in
	 *            before the call.
	 */
	private ImmutableStackEntry stackEntry(Location location, int scope,
			int dyscopeIdentifier) {
		return new ImmutableStackEntry(location, scope, dyscopeIdentifier);
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
	 * @return new dynamic scopes or null
	 */
	private ImmutableDynamicScope[] updateProcessReferencesInScopes(
			State state, int[] oldToNewPidMap) {
		Map<SymbolicExpression, SymbolicExpression> procSubMap = procSubMap(oldToNewPidMap);
		UnaryOperator<SymbolicExpression> substituter = universe
				.mapSubstituter(procSubMap);
		ImmutableDynamicScope[] newScopes = null;
		int numScopes = state.numDyscopes();

		for (int i = 0; i < numScopes; i++) {
			ImmutableDynamicScope dynamicScope = (ImmutableDynamicScope) state
					.getDyscope(i);
			Scope staticScope = dynamicScope.lexicalScope();
			Collection<Variable> procrefVariableIter = staticScope
					.variablesWithProcrefs();
			SymbolicExpression[] newValues = null;
			BitSet oldBitSet = dynamicScope.getReachers();
			BitSet newBitSet = updateBitSet(oldBitSet, oldToNewPidMap);

			for (Variable variable : procrefVariableIter) {
				int vid = variable.vid();
				SymbolicExpression oldValue = dynamicScope.getValue(vid);
				SymbolicExpression newValue = substituter.apply(oldValue);

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
						newScopes[j] = (ImmutableDynamicScope) state
								.getDyscope(j);
				}
				if (newValues == null)
					newScopes[i] = dynamicScope.setReachers(newBitSet);
				else
					newScopes[i] = new ImmutableDynamicScope(staticScope,
							dynamicScope.getParent(), 0, newValues, newBitSet,
							dynamicScope.identifier());
			} else if (newScopes != null) {
				newScopes[i] = dynamicScope;
			}
		}
		return newScopes;
	}

	private Set<SymbolicExpression> reachableHeapObjectsOfState(State state) {
		Set<SymbolicExpression> reachable = new LinkedHashSet<>();
		int numDyscopes = state.numDyscopes();

		for (int i = 0; i < numDyscopes; i++) {
			DynamicScope dyscope = state.getDyscope(i);
			int numVars = dyscope.numberOfValues();

			for (int vid = 0; vid < numVars; vid++) {
				SymbolicExpression value = dyscope.getValue(vid);

				reachableHeapObjectsOfValue(state, value, reachable);
			}
		}
		return reachable;
	}

	@SuppressWarnings("incomplete-switch")
	private void reachableHeapObjectsOfValue(State state,
			SymbolicExpression value, Set<SymbolicExpression> reachable) {
		if (value.isNull())
			return;
		else if (!this.isPointer(value)) {
			int numArgs = value.numArguments();

			for (int i = 0; i < numArgs; i++) {
				SymbolicObject arg = value.argument(i);
				SymbolicObjectKind kind = arg.symbolicObjectKind();

				switch (kind) {
				case BOOLEAN:
				case INT:
				case NUMBER:
				case STRING:
				case CHAR:
				case TYPE:
				case TYPE_SEQUENCE:
					break;
				default:
					switch (kind) {
					case EXPRESSION:
						reachableHeapObjectsOfValue(state,
								(SymbolicExpression) arg, reachable);
						break;
					case EXPRESSION_COLLECTION: {
						Iterator<? extends SymbolicExpression> iter = ((SymbolicCollection<?>) arg)
								.iterator();

						while (iter.hasNext()) {
							SymbolicExpression expr = iter.next();

							reachableHeapObjectsOfValue(state, expr, reachable);
						}
					}
					}
				}
			}
		} else if (value.operator() != SymbolicOperator.CONCRETE) {
			return;
		} else if (symbolicUtil.isHeapPointer(value)) {
			SymbolicExpression heapObjPtr = this.symbolicUtil
					.heapMemUnit(value);

			// if (!reachable.contains(heapObjPtr))
			reachable.add(heapObjPtr);
		} else if (this.symbolicUtil.isDerefablePointer(value)) {
			// other pointers
			int dyscopeId = this.symbolicUtil.getDyscopeId(null, value);
			int vid = this.symbolicUtil.getVariableId(null, value);
			ReferenceExpression reference = this.symbolicUtil.getSymRef(value);
			SymbolicExpression varValue = state
					.getVariableValue(dyscopeId, vid);
			SymbolicExpression objectValue;

			try {
				objectValue = this.universe.dereference(varValue, reference);
			} catch (SARLException e) {
				return;
			}
			reachableHeapObjectsOfValue(state, objectValue, reachable);
		}
	}

	private boolean isPointer(SymbolicExpression value) {
		if (value.type().equals(typeFactory.pointerSymbolicType()))
			return true;
		return false;
	}

	private boolean hasNonEmptyHeaps(State state) {
		int numDyscopes = state.numDyscopes();

		for (int dyscopeId = 0; dyscopeId < numDyscopes; dyscopeId++) {
			DynamicScope dyscope = state.getDyscope(dyscopeId);
			SymbolicExpression heap = dyscope.getValue(0);

			if (!heap.isNull())
				return true;
		}
		return false;
	}

	private void computeOldToNewHeapPointers(State state,
			Map<SymbolicExpression, SymbolicExpression> heapMemUnitsMap,
			Map<SymbolicExpression, SymbolicExpression> oldToNewExpressions) {
		if (heapMemUnitsMap.size() < 1)
			return;
		else {
			int numDyscopes = state.numDyscopes();

			for (int dyscopeID = 0; dyscopeID < numDyscopes; dyscopeID++) {
				DynamicScope dyscope = state.getDyscope(dyscopeID);
				int numVars = dyscope.numberOfValues();

				for (int vid = 0; vid < numVars; vid++) {
					computeNewHeapPointer(dyscope.getValue(vid),
							heapMemUnitsMap, oldToNewExpressions);
				}
			}
		}
	}

	@SuppressWarnings("incomplete-switch")
	private void computeNewHeapPointer(SymbolicExpression value,
			Map<SymbolicExpression, SymbolicExpression> heapMemUnitsMap,
			Map<SymbolicExpression, SymbolicExpression> oldToNewHeapPointers) {
		if (value.isNull())
			return;
		else if (!this.isPointer(value)) {
			int numArgs = value.numArguments();

			for (int i = 0; i < numArgs; i++) {
				SymbolicObject arg = value.argument(i);
				SymbolicObjectKind kind = arg.symbolicObjectKind();

				switch (kind) {
				case BOOLEAN:
				case INT:
				case NUMBER:
				case STRING:
				case CHAR:
				case TYPE:
				case TYPE_SEQUENCE:
					break;
				default:
					switch (kind) {
					case EXPRESSION:
						computeNewHeapPointer((SymbolicExpression) arg,
								heapMemUnitsMap, oldToNewHeapPointers);
						break;
					case EXPRESSION_COLLECTION: {
						Iterator<? extends SymbolicExpression> iter = ((SymbolicCollection<?>) arg)
								.iterator();

						while (iter.hasNext()) {
							SymbolicExpression expr = iter.next();

							computeNewHeapPointer(expr, heapMemUnitsMap,
									oldToNewHeapPointers);
						}
					}
					}
				}
			}
		} else if (symbolicUtil.isHeapPointer(value)) {
			SymbolicExpression heapObjPtr = this.symbolicUtil
					.heapMemUnit(value);
			SymbolicExpression newHeapObjPtr = heapMemUnitsMap.get(heapObjPtr);

			if (newHeapObjPtr != null
					&& !oldToNewHeapPointers.containsKey(value)) {
				if (!symbolicUtil.isDefinedPointer(newHeapObjPtr))
					oldToNewHeapPointers.put(value, newHeapObjPtr);
				else {
					ReferenceExpression ref = symbolicUtil
							.referenceToHeapMemUnit(value);
					SymbolicExpression newPointer = symbolicUtil.extendPointer(
							newHeapObjPtr, ref);

					oldToNewHeapPointers.put(value, newPointer);
				}
			}
		}
	}

	private void addOldToNewHeapMemUnits(Map<Integer, Integer> oldID2NewID,
			SymbolicExpression heapPointer, ReferenceExpression fieldRef,
			Map<SymbolicExpression, SymbolicExpression> oldToNewMap) {
		for (Map.Entry<Integer, Integer> entry : oldID2NewID.entrySet()) {
			ReferenceExpression oldRef = universe.arrayElementReference(
					fieldRef, universe.integer(entry.getKey()));
			SymbolicExpression oldPtr = this.symbolicUtil.setSymRef(
					heapPointer, oldRef);
			ReferenceExpression newRef = universe.arrayElementReference(
					fieldRef, universe.integer(entry.getValue()));
			SymbolicExpression newPtr = this.symbolicUtil.setSymRef(
					heapPointer, newRef);

			oldToNewMap.put(oldPtr, newPtr);
		}
	}

	/**
	 * Rename all symbolic constants of the state. Trying to use the new
	 * interface (canonicRenamer) provided by SARL.
	 * 
	 * @param state
	 * @return
	 */
	@SuppressWarnings("unused")
	private ImmutableState collectSymbolicConstants(State state,
			boolean collectHeaps) {
		ImmutableState theState = (ImmutableState) state;
		int numDyscopes = theState.numDyscopes();
		UnaryOperator<SymbolicExpression> nameSubstituter = universe
				.canonicalRenamer("X", this.isReservedSymbolicConstant);
		ImmutableDynamicScope[] newScopes = new ImmutableDynamicScope[numDyscopes];
		boolean change = false;

		for (int dyscopeId = 0; dyscopeId < numDyscopes; dyscopeId++) {
			ImmutableDynamicScope oldScope = theState.getDyscope(dyscopeId);
			ImmutableDynamicScope newScope = oldScope
					.updateSymbolicConstants(nameSubstituter);

			change = change || newScope != oldScope;
			newScopes[dyscopeId] = newScope;
		}
		if (!change)
			newScopes = null;

		BooleanExpression oldPathCondition = theState.getPathCondition();
		BooleanExpression newPathCondition = (BooleanExpression) nameSubstituter
				.apply(oldPathCondition);

		if (oldPathCondition == newPathCondition)
			newPathCondition = null;
		else
			change = true;
		if (change)
			theState = ImmutableState.newState(theState, null, newScopes,
					newPathCondition);
		return theState;
	}

	@Override
	public ImmutableState setLocation(State state, int pid, Location location) {
		return this.setLocation(state, pid, location, false);
	}

	@Override
	public MemoryUnitFactory memUnitFactory() {
		return this.memUnitFactory;
	}

	@Override
	public State incrementNumSymbolicConstants(State state) {
		Variable symbolicConstantVar = state.getDyscope(0).lexicalScope()
				.variable(ModelConfiguration.SYMBOLIC_CONSTANT_COUNTER);
		SymbolicExpression countValue = state.getVariableValue(0,
				symbolicConstantVar.vid()), newCount;

		if (countValue.isNull())
			newCount = universe.oneInt();
		else
			newCount = universe.add((NumericExpression) countValue,
					universe.oneInt());
		return this.setVariable(state, symbolicConstantVar.vid(), 0, newCount);
	}

	@Override
	public int numSymbolicConstants(State state) {
		Variable symbolicConstantVar = state.getDyscope(0).lexicalScope()
				.variable(ModelConfiguration.SYMBOLIC_CONSTANT_COUNTER);
		SymbolicExpression countValue = state.getVariableValue(0,
				symbolicConstantVar.vid());

		if (countValue.isNull())
			return 0;

		IntegerNumber countNum = (IntegerNumber) universe
				.extractNumber((NumericExpression) countValue);

		return countNum.intValue();
	}

	@Override
	public Map<Variable, SymbolicExpression> inputVariableValueMap(State state) {
		Map<Variable, SymbolicExpression> result = new LinkedHashMap<>();

		for (Variable variable : this.inputVariables) {
			assert variable.scope().id() == 0;
			result.put(variable, state.getVariableValue(0, variable.vid()));
		}
		return result;
	}

	/* **************** MPI contracts related functions ******************* */
	@Override
	public ImmutableState commitUpdatedChannelsToEntries(State state,
			int queueId, SymbolicExpression[] newBuffers) {
		ImmutableState tmpState = (ImmutableState) state;
		ImmutableCollectiveSnapshotsEntry[][] queues = tmpState
				.getSnapshotsQueues();
		ImmutableCollectiveSnapshotsEntry[] queue;
		int queueLength;

		assert queues != null : "Commite updated message channels to a "
				+ "state with empty collective queue";
		assert queues.length > queueId;
		queue = queues[queueId];
		assert queue != null : "Commite updated message channels to an unexisted collective queue";
		queueLength = queue.length;
		assert queueLength == newBuffers.length;
		for (int i = 0; i < queueLength; i++) {
			ImmutableCollectiveSnapshotsEntry entry = queue[i];

			entry = entry.setMsgBuffers(newBuffers[i]);
			queue[i] = entry;
		}
		queues[queueId] = queue;
		return tmpState.setSnapshotsQueues(queues);
	}

	@Override
	public ImmutableState mergeMonostates(State state,
			ImmutableCollectiveSnapshotsEntry entry) {
		ImmutableState newState;
		ImmutableMonoState[] monoStates = entry.getMonoStates();
		int numProcesses = entry.numMonoStates();
		ImmutableProcessState[] processes = new ImmutableProcessState[numProcesses];
		ImmutableDynamicScope[][] localDyscopes = new ImmutableDynamicScope[numProcesses][];
		ImmutableDynamicScope[] dyscopes;
		// A list of "oldToNew" tables, each process has its own table.
		int[][] dyscopeOldToNews = new int[numProcesses][];
		int totalDyscopeCounter = 0;
		int[] procOldToNew = new int[entry.getMaxPid() + 1];
		BooleanExpression pathCondition = universe.trueExpression();

		for (int place = 0; place < numProcesses; place++) {
			ImmutableMonoState monoState = monoStates[place];
			ImmutableProcessState process = monoState.getProcessState();
			int oldPid = process.getPid();
			int numDyscopes = monoState.numDyscopes();

			processes[place] = process.setPid(place);
			procOldToNew[oldPid] = place;
			localDyscopes[place] = this.updateProcessReferencesInScopes(
					monoState, procOldToNew);
			// computes oldToNew arrays
			dyscopeOldToNews[place] = new int[localDyscopes[place].length];
			for (int sid = 0; sid < numDyscopes; sid++)
				dyscopeOldToNews[place][sid] = totalDyscopeCounter++;
			pathCondition = universe.and(pathCondition,
					monoState.getPathCondition());
		}
		dyscopes = new ImmutableDynamicScope[totalDyscopeCounter];
		// re-numbers dyscopes
		for (int place = 0; place < numProcesses; place++) {
			renumberDyscopes(localDyscopes[place], dyscopeOldToNews[place],
					dyscopes);
			processes[place] = processes[place]
					.updateDyscopes(dyscopeOldToNews[place]);
		}
		newState = new ImmutableState(processes, dyscopes, pathCondition);
		newState = newState.setSnapshotsQueues(((ImmutableState) state)
				.getSnapshotsQueues());
		return newState;
	}

	// pre-condition: entry exists.
	@Override
	public ImmutableState addToCollectiveSnapshotsEntry(ImmutableState state,
			int pid, int place, int queueID, int entryPos, Expression assertion) {
		ImmutableCollectiveSnapshotsEntry[] queue = state.getSnapshots(queueID);
		ImmutableCollectiveSnapshotsEntry entry;
		ImmutableMonoState snapshot;

		assert queue != null;
		entry = queue[entryPos];
		// take a snapshot
		snapshot = takeSnapshot((ImmutableState) state, pid);
		entry = entry.insertMonoState(place, snapshot, assertion);
		queue[entryPos] = entry;
		return state.updateQueue(queueID, queue);
	}

	@Override
	public ImmutableState createCollectiveSnapshotsEnrty(ImmutableState state,
			int pid, int numProcesses, int place, int queueID,
			Expression assertion, SymbolicExpression channels, ContractKind kind) {
		ImmutableCollectiveSnapshotsEntry[] queue = state.getSnapshots(queueID);
		ImmutableCollectiveSnapshotsEntry[] newQueue;
		ImmutableCollectiveSnapshotsEntry entry = new ImmutableCollectiveSnapshotsEntry(
				numProcesses, universe, kind);
		ImmutableMonoState snapshot;

		// take a snapshot
		snapshot = this.takeSnapshot((ImmutableState) state, pid);
		entry = entry.insertMonoState(place, snapshot, assertion);
		entry = entry.setMsgBuffers(channels);
		assert queue != null;
		newQueue = new ImmutableCollectiveSnapshotsEntry[queue.length + 1];
		for (int i = 0; i < queue.length; i++)
			newQueue[i] = queue[i];
		newQueue[queue.length] = entry;
		return state.updateQueue(queueID, newQueue);
	}

	@Override
	public State dequeueCollectiveSnapshotsEntry(State state, int queueID) {
		ImmutableState immuState = (ImmutableState) state;
		ImmutableCollectiveSnapshotsEntry[] queue = immuState
				.getSnapshots(queueID);

		assert queue != null && queue.length > 0 : "Dequeues on an empty queue";
		if (queue.length == 1)
			queue = new ImmutableCollectiveSnapshotsEntry[0];
		else
			queue = Arrays.copyOfRange(queue, 1, queue.length - 1);
		return immuState.updateQueue(queueID, queue);
	}

	@Override
	public ImmutableCollectiveSnapshotsEntry peekCollectiveSnapshotsEntry(
			State state, int queueID) {
		ImmutableState immuState = (ImmutableState) state;
		ImmutableCollectiveSnapshotsEntry[] queue = immuState
				.getSnapshots(queueID);
		ImmutableCollectiveSnapshotsEntry entry;
		;

		assert queue != null && queue.length > 0 : "Peeks on an empty queue";
		entry = queue[0];
		return entry;
	}

	@Override
	public ImmutableCollectiveSnapshotsEntry[] getSnapshotsQueue(State state,
			int queueID) {
		return ((ImmutableState) state).getSnapshots(queueID);
	}

	/**
	 * Renumbers and re-arranges an array of {@link DynamicScope} with an
	 * "oldToNew" array as a dictionary which is used for looking up new IDs
	 * (indices) by indexing old IDs (indices).
	 * 
	 * @precondition The largest new index in "oldToNew" table should be less
	 *               than the length of the output array.
	 * @param oldDyscopes
	 *            An array of old {@link DynamicScope}
	 * @param oldToNew
	 *            An array as a dictionary which is used for looking up new IDs
	 *            by indexing old IDs.
	 * @param outputDyscopes
	 *            An array of new {@link DynamicScope}
	 */
	private void renumberDyscopes(ImmutableDynamicScope[] oldDyscopes,
			int[] oldToNew, ImmutableDynamicScope[] outputDyscopes) {
		IntArray key = new IntArray(oldToNew);
		UnaryOperator<SymbolicExpression> substituter = dyscopeSubMap.get(key);
		int numOldDyscopes = oldDyscopes.length;

		if (null == substituter) {
			substituter = universe.mapSubstituter(scopeSubMap(oldToNew));
			dyscopeSubMap.put(key, substituter);
		}
		for (int i = 0; i < numOldDyscopes; i++) {
			int newId = oldToNew[i];

			if (-1 != newId) {
				ImmutableDynamicScope oldScope = oldDyscopes[i];
				int oldParent = oldScope.getParent();
				int oldParentIdentifier = oldScope.identifier();

				outputDyscopes[newId] = oldScope.updateDyscopeIds(substituter,
						universe, oldParent < 0 ? oldParent
								: oldToNew[oldParent], oldParentIdentifier);
			}
		}
	}

	/**
	 * Take a snapshot for a process specified with its PID on a
	 * {@link ImmutableState}. For the {@link ProcessState} associates to the
	 * PID, this function will take its {@link DynamicScope}s with following
	 * rules:<br>
	 * <ol>
	 * <li>1. The {@link DynamicScope} d0 associates to the top frame of the
	 * call stack of the process.</li>
	 * <li>2. All ancestors of d0. (It's based on the assumption that there is
	 * no shared storage among MPI processes.)</li>
	 * 
	 * @precondition: State and PID must be a valid one.
	 * @postcondition: true.
	 * 
	 * @param state
	 *            The global state where the snapshot is taken
	 * @param pid
	 *            The PID for the process whose state is taken as a snapshot
	 * @return A new {@link ImmutableMonoState} which is a snapshot for a
	 *         process.
	 */
	private ImmutableMonoState takeSnapshot(ImmutableState state, int pid) {
		ImmutableProcessState processState = state.getProcessState(pid);
		ImmutableProcessState newProcessState;
		ImmutableMonoState snapshot;
		ImmutableDynamicScope newDyscopes[];
		ImmutableDynamicScope[] oldDyscopes;
		StackEntry[] newMonoFrame = new StackEntry[1];
		BooleanExpression pathCondition;
		Iterator<StackEntry> iter;
		// upper bound of number of dyscopes in the snapshot:
		int numDyscopesInState = state.numDyscopes();
		int oldToNew[];
		int newDyscopesCounter = 0;

		newDyscopes = new ImmutableDynamicScope[numDyscopesInState];
		oldToNew = new int[numDyscopesInState];
		// initializes oldToNew array
		for (int i = 0; i < numDyscopesInState; i++)
			oldToNew[i] = -1;
		oldDyscopes = new ImmutableDynamicScope[numDyscopesInState];
		iter = processState.getStackEntries().iterator();
		if (iter.hasNext()) {
			StackEntry topFrame = iter.next();
			int oldSid = topFrame.scope();
			ImmutableDynamicScope currentDyscope;

			newMonoFrame[0] = topFrame;
			while (oldSid != -1) {
				currentDyscope = state.getDyscope(oldSid);
				oldDyscopes[oldSid] = currentDyscope;
				oldToNew[oldSid] = newDyscopesCounter++;
				oldSid = currentDyscope.getParent();
			}
		}
		renumberDyscopes(oldDyscopes, oldToNew, newDyscopes);
		processState = (ImmutableProcessState) processState
				.setStackEntries(newMonoFrame);
		newProcessState = processState.updateDyscopes(oldToNew);
		// TODO: Does the path condition contain references on other processes ?
		pathCondition = state.getPathCondition();
		newDyscopes = Arrays.copyOf(newDyscopes, newDyscopesCounter);
		snapshot = new ImmutableMonoState(newProcessState, newDyscopes,
				pathCondition);
		return snapshot;
	}
}
