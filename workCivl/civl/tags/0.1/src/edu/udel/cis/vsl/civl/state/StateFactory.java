package edu.udel.cis.vsl.civl.state;

import java.util.BitSet;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Vector;

import edu.udel.cis.vsl.civl.model.IF.Function;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.type.ArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.PrimitiveType;
import edu.udel.cis.vsl.civl.model.IF.type.ProcessType;
import edu.udel.cis.vsl.civl.model.IF.type.Type;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * Factory to create all state objects.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * @author Timothy J. McClory (tmcclory)
 * 
 */
public class StateFactory implements StateFactoryIF {

	// *************************** Fields *****************************

	private int stateCount = 0;

	private SymbolicUniverse symbolicUniverse;

	private Map<DynamicScope, DynamicScope> scopeMap = new HashMap<DynamicScope, DynamicScope>();

	private Map<Process, Process> processMap = new HashMap<Process, Process>();

	private Map<State, State> stateMap = new HashMap<State, State>();

	private String pidPrefix = "PID_";

	private SymbolicTupleType processType;

	// *************************** Constructors ***********************

	/**
	 * Factory to create all state objects.
	 */
	public StateFactory(SymbolicUniverse symbolicUniverse) {
		List<SymbolicType> processTypeList = new Vector<SymbolicType>();

		this.symbolicUniverse = symbolicUniverse;
		processTypeList.add(symbolicUniverse.integerType());
		processType = symbolicUniverse.tupleType(
				symbolicUniverse.stringObject("process"), processTypeList);
	}

	// ************************* Helper Methods ***********************

	/**
	 * Implements the flyweight pattern: if there already exists a scope which
	 * is equivalent to the given scope, return that one, otherwise, add scope
	 * to table and return it.
	 * 
	 * @param map
	 *            the map used to record the scopes
	 * @param expression
	 *            the scope to be flyweighted
	 * @return the unique representative of the scope or the scope itself
	 */
	private DynamicScope canonic(DynamicScope scope) {
		DynamicScope old = scopeMap.get(scope);

		if (old == null) {
			scope.canonic = true;
			scopeMap.put(scope, scope);
			return scope;
		}
		return old;
	}

	/**
	 * Implements the flyweight pattern: if there already exists a process which
	 * is equivalent to the given process, return that one, otherwise, add
	 * process to table and return it.
	 * 
	 * @param map
	 *            the map used to record the processes
	 * @param expression
	 *            the process to be flyweighted
	 * @return the unique representative of the process or the process itself
	 */
	private Process canonic(Process process) {
		Process old = processMap.get(process);

		if (old == null) {
			process.canonic = true;
			processMap.put(process, process);
			return process;
		}
		return old;
	}

	private Process process(int id, StackEntry[] stack) {
		return canonic(new Process(id, stack));
	}

	private SymbolicExpression[] initialValues(Scope lexicalScope,
			int dynamicScopeId) {
		SymbolicExpression[] values = new SymbolicExpression[lexicalScope
				.variables().size()];

		for (int i = 0; i < values.length; i++) {
			Variable v = lexicalScope.getVariable(i);

			if (v.type() instanceof ArrayType) {
				StringObject name = symbolicUniverse.stringObject("A_s"
						+ dynamicScopeId + "v" + i);
				SymbolicType type = arrayType((ArrayType) v.type());

				values[i] = symbolicUniverse.symbolicConstant(name, type);
			} else if (v.isExtern()) {
				StringObject name = symbolicUniverse.stringObject("s"
						+ dynamicScopeId + "v" + i);
				SymbolicType type = null;

				if (v.type() instanceof PrimitiveType) {
					switch (((PrimitiveType) v.type()).primitiveType()) {
					case INT:
						type = symbolicUniverse.integerType();
						break;
					case BOOL:
						type = symbolicUniverse.booleanType();
						break;
					case REAL:
						type = symbolicUniverse.realType();
						break;
					case STRING:
						// TODO: Handle this.
					default:
						break;
					}
				} else {
					throw new RuntimeException("Unimplemented input type: "
							+ v.type());
				}

				values[i] = symbolicUniverse.symbolicConstant(name, type);
			}
		}
		return values;
	}

	private DynamicScope dynamicScope(Scope lexicalScope, int parent,
			SymbolicExpression[] variableValues, BitSet reachers) {
		return canonic(new DynamicScope(lexicalScope, parent, variableValues,
				reachers));
	}

	/**
	 * A dynamic scope.
	 * 
	 * @param lexicalScope
	 *            The lexical scope corresponding to this dynamic scope.
	 * @param parent
	 *            The parent of this dynamic scope. -1 only for the topmost
	 *            dynamic scope.
	 * @return A new dynamic scope.
	 */
	private DynamicScope dynamicScope(Scope lexicalScope, int parent,
			int dynamicScopeId, BitSet reachers) {
		return dynamicScope(lexicalScope, parent,
				initialValues(lexicalScope, dynamicScopeId), reachers);
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
	private StackEntry stackEntry(Location location, int scope) {
		return new StackEntry(location, scope);
	}

	/**
	 * Get the symbolic type of an array.
	 * 
	 * @param type
	 *            The model array type.
	 * @return The symbolic array type.
	 */
	private SymbolicType arrayType(ArrayType type) {
		Type baseType = type.baseType();

		if (baseType instanceof ArrayType) {
			return symbolicUniverse.arrayType(arrayType((ArrayType) baseType));
		} else if (baseType instanceof PrimitiveType) {
			switch (((PrimitiveType) baseType).primitiveType()) {
			case INT:
				return symbolicUniverse.arrayType(symbolicUniverse
						.integerType());
			case BOOL:
				return symbolicUniverse.arrayType(symbolicUniverse
						.booleanType());
			case REAL:
				return symbolicUniverse.arrayType(symbolicUniverse.realType());
			case STRING:
				// TODO: Handle this.
			default:
				break;
			}
		} else if (baseType instanceof ProcessType) {
			return symbolicUniverse.arrayType(processType);
		}
		return null;
	}

	private State collectScopes(State state) {
		int oldNumScopes = state.numScopes();
		int[] oldToNew = numberScopes(state);
		boolean change = false;
		int newNumScopes = 0;

		for (int i = 0; i < oldNumScopes; i++) {
			int id = oldToNew[i];

			if (id >= 0)
				newNumScopes++;
			if (!change && id != i)
				change = true;
		}
		if (!change)
			return state;

		DynamicScope[] newScopes = new DynamicScope[newNumScopes];
		int numProcs = state.numProcs();
		Process[] newProcesses = new Process[numProcs];

		for (int i = 0; i < oldNumScopes; i++) {
			int newId = oldToNew[i];

			if (newId >= 0) {
				DynamicScope oldScope = state.getScope(i);
				int oldParent = oldScope.parent();
				int newParent = (oldParent < 0 ? oldParent
						: oldToNew[oldParent]);
				DynamicScope newScope = (oldParent == newParent ? oldScope
						: canonic(oldScope.changeParent(newParent)));

				newScopes[newId] = newScope;
			}
		}
		for (int pid = 0; pid < numProcs; pid++) {
			Process oldProcess = state.process(pid);
			int stackSize = oldProcess.stackSize();
			StackEntry[] newStack = new StackEntry[stackSize];
			boolean stackChange = false;

			for (int j = 0; j < stackSize; j++) {
				StackEntry oldFrame = oldProcess.getStackEntry(j);
				int oldScope = oldFrame.scope();
				int newScope = oldToNew[oldScope];

				if (oldScope == newScope) {
					newStack[j] = oldFrame;
				} else {
					stackChange = true;
					newStack[j] = stackEntry(oldFrame.location(), newScope);
				}
			}
			if (stackChange)
				newProcesses[pid] = process(pid, newStack);
			else
				newProcesses[pid] = oldProcess;
		}
		return new State(newProcesses, newScopes, state.pathCondition());
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
	private int[] numberScopes(State state) {
		int numScopes = state.numScopes();
		int numProcs = state.numProcs();
		int[] oldToNew = new int[numScopes];
		int nextScopeId = 0;

		for (int i = 0; i < numScopes; i++)
			oldToNew[i] = -1;
		for (int pid = 0; pid < numProcs; pid++) {
			Process process = state.process(pid);
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

	// *********************** Exported Methods ***********************

	@Override
	public State canonic(State state) {
		State old = stateMap.get(state);

		if (old == null) {
			state.setCanonicId(stateCount);
			stateCount++;
			stateMap.put(state, state);
			return state;
		}
		return old;
	}

	@Override
	public State initialState(Model model) {
		State state = new State(new Process[0], new DynamicScope[0],
				symbolicUniverse.trueExpression());
		Function function = model.system();
		int numArgs = function.parameters().size();
		SymbolicExpression[] arguments = new SymbolicExpression[numArgs];

		// TODO: how to initialize the arguments to system function?
		state = addProcess(state, function, arguments, -1);
		return canonic(state);
	}

	/**
	 * Update the value of a dynamic variable in the state.
	 * 
	 * @param state
	 *            The old state.
	 * @param variable
	 *            The dynamic variable to update.
	 * @param pid
	 *            The pid of the process containing the variable.
	 * @param value
	 *            The new value of the dynamic variable.
	 * @return A new state that is the old state modified by updating the value
	 *         of the variable.
	 */
	@Override
	public State setVariable(State state, Variable variable, int pid,
			SymbolicExpression value) {
		int scopeId = state.getScopeId(pid, variable);
		return setVariable(state, variable, scopeId, pid, value);
	}

	/**
	 * Update the value of a dynamic variable in the state.
	 * 
	 * @param state
	 *            The old state.
	 * @param variable
	 *            The dynamic variable to update.
	 * @param scopeID
	 *            The ID of the scope containing the variable. This version of
	 *            the method is useful when setting the target of a pointer. For
	 *            a variable in the current lexical scope, use the version of
	 *            the method without this argument.
	 * @param pid
	 *            The pid of the process containing the variable.
	 * @param value
	 *            The new value of the dynamic variable.
	 * @return A new state that is the old state modified by updating the value
	 *         of the variable.
	 */
	@Override
	public State setVariable(State state, Variable variable, int scopeId,
			int pid, SymbolicExpression value) {
		DynamicScope oldScope = state.getScope(scopeId);
		DynamicScope[] newScopes = state.copyScopes();
		SymbolicExpression[] newValues = oldScope.copyValues();
		DynamicScope newScope;

		newValues[variable.vid()] = value;
		newScope = dynamicScope(oldScope.lexicalScope(), oldScope.parent(),
				newValues, oldScope.reachers());
		newScopes[scopeId] = newScope;
		return new State(state, newScopes);
	}

	@Override
	public State addProcess(State state, Function function,
			SymbolicExpression[] arguments, int callerPid) {
		int numProcs = state.numProcs();
		Process[] newProcesses;

		newProcesses = state.copyAndExpandProcesses();
		newProcesses[numProcs] = process(numProcs, new StackEntry[0]);
		state = new State(state, newProcesses);
		return pushCallStack2(state, numProcs, function, arguments, callerPid);
	}

	@Override
	public State removeProcess(State state, int pid) {
		int numProcs = state.numProcs();
		Process[] newProcesses = new Process[numProcs - 1];
		DynamicScope[] newScopes = null;

		for (int i = 0; i < pid; i++)
			newProcesses[i] = state.process(i);
		{
			int[] oldToNewPidMap = new int[numProcs];

			for (int i = pid; i < numProcs - 1; i++)
				newProcesses[i] = canonic(new Process(state.process(i + 1), i));
			for (int i = 0; i < pid; i++)
				oldToNewPidMap[i] = i;
			oldToNewPidMap[pid] = -1;
			for (int i = pid + 1; i < numProcs; i++)
				oldToNewPidMap[i] = i - 1;
			newScopes = updateProcessReferencesInScopes(state, oldToNewPidMap);
		}
		state = new State(state, newProcesses, newScopes, null);
		return collectScopes(state);
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
	private DynamicScope[] updateProcessReferencesInScopes(State state,
			int[] oldToNewPidMap) {
		DynamicScope[] newScopes = null;
		int numScopes = state.numScopes();

		for (int i = 0; i < numScopes; i++) {
			DynamicScope dynamicScope = state.getScope(i);
			Scope staticScope = dynamicScope.lexicalScope();
			Collection<Variable> procrefVariableIter = staticScope
					.variablesWithProcrefs();
			SymbolicExpression[] newValues = null;
			BitSet oldBitSet = dynamicScope.reachers();
			BitSet newBitSet = updateBitSet(oldBitSet, oldToNewPidMap);

			for (Variable variable : procrefVariableIter) {
				int vid = variable.vid();
				SymbolicExpression oldValue = dynamicScope.getValue(vid);
				SymbolicExpression newValue = substituteIntegers(
						variable.type(), oldValue, oldToNewPidMap);

				if (oldValue != newValue) {
					if (newValues == null)
						newValues = dynamicScope.copyValues();
					newValues[vid] = newValue;
				}
			}
			if (newValues != null || newBitSet != oldBitSet) {
				if (newScopes == null) {
					newScopes = new DynamicScope[numScopes];
					for (int j = 0; j < i; j++)
						newScopes[j] = state.getScope(j);
				}
				if (newValues == null)
					newScopes[i] = canonic(dynamicScope
							.changeReachers(newBitSet));
				else
					newScopes[i] = dynamicScope(staticScope,
							dynamicScope.parent(), newValues, newBitSet);
			} else if (newScopes != null) {
				newScopes[i] = dynamicScope;
			}
		}
		return newScopes;
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
	 * Substitutes PIDs in a symbolic expression (value).
	 * 
	 * If given expression is null, returns null.
	 * 
	 * Otherwise, searches for PID values in the expression, and returns a
	 * symbolic expression obtained by subsituting new values for the old ones,
	 * based on the oldToNew map and the type.
	 * 
	 * @param type
	 *            the CIVL type of the given value
	 * @param value
	 *            a symbolic expression which is the value of a variable whose
	 *            type is "type"
	 * @param oldToNew
	 *            an array of ints of length n, where n must be greater than any
	 *            PID value that could occur in value. The element at position i
	 *            will be substituted for a PID value of i.
	 * 
	 * @return a symbolic expression with new PID values, or null if the given
	 *         symbolic expression was null
	 */
	private SymbolicExpression substituteIntegers(Type type,
			SymbolicExpression value, int[] oldToNew) {
		Map<SymbolicConstant, SymbolicExpression> substitutions = new HashMap<SymbolicConstant, SymbolicExpression>();
		if (value == null)
			return null;

		for (int i = 0; i < oldToNew.length; i++) {
			StringObject oldString = symbolicUniverse.stringObject(pidPrefix
					+ i);
			SymbolicConstant oldConstant = symbolicUniverse.symbolicConstant(
					oldString, processType);
			StringObject newString = symbolicUniverse.stringObject(pidPrefix
					+ oldToNew[i]);
			SymbolicConstant newConstant = symbolicUniverse.symbolicConstant(
					newString, processType);

			substitutions.put(oldConstant, newConstant);
		}
		return symbolicUniverse.substitute(value, substitutions);
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
	 * TODO: update reachable
	 * 
	 * @param state
	 * @param pid
	 * @param location
	 * @return
	 */
	public State setLocation(State state, int pid, Location location) {
		Process[] processArray = state.processes();
		int dynamicScopeId = state.process(pid).scope();
		DynamicScope dynamicScope = state.getScope(dynamicScopeId);
		Scope ss0 = dynamicScope.lexicalScope();
		Scope ss1 = location.scope();

		if (ss0 == ss1) {
			processArray[pid] = canonic(state.process(pid).replaceTop(
					stackEntry(location, dynamicScopeId)));
			return new State(state, processArray);
		} else {
			Scope[] joinSequence = joinSequence(ss0, ss1);
			Scope join = joinSequence[0];

			// iterate UP...
			while (dynamicScope.lexicalScope() != join) {
				dynamicScopeId = state.getParentId(dynamicScopeId);
				if (dynamicScopeId < 0)
					throw new RuntimeException("State is inconsistent");
				dynamicScope = state.getScope(dynamicScopeId);
			}
			if (joinSequence.length == 1) {
				processArray[pid] = canonic(state.process(pid).replaceTop(
						stackEntry(location, dynamicScopeId)));
				state = new State(state, processArray);
			} else {
				// iterate DOWN, adding new dynamic scopes...
				int oldNumScopes = state.numScopes();
				int newNumScopes = oldNumScopes + joinSequence.length - 1;
				int index = 0;
				DynamicScope[] newScopes = new DynamicScope[newNumScopes];
				Process process = processArray[pid];

				for (; index < oldNumScopes; index++)
					newScopes[index] = state.getScope(index);
				for (int i = 1; i < joinSequence.length; i++) {
					// only this process can reach the new dyscope
					BitSet reachers = new BitSet(processArray.length);

					reachers.set(pid);
					newScopes[index] = dynamicScope(joinSequence[i],
							dynamicScopeId, index, reachers);
					dynamicScopeId = index;
					index++;
				}
				process = canonic(process.replaceTop(stackEntry(location,
						dynamicScopeId)));
				setReachablesForProc(newScopes, process);
				processArray[pid] = process;
				state = new State(processArray, newScopes,
						state.pathCondition());
			}
			return collectScopes(state);
		}
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
	private void setReachablesForProc(DynamicScope[] dynamicScopes,
			Process process) {
		int stackSize = process.stackSize();
		int numScopes = dynamicScopes.length;
		boolean reached[] = new boolean[numScopes];
		int pid = process.id();

		for (int i = 0; i < stackSize; i++) {
			StackEntry frame = process.getStackEntry(i);
			int id = frame.scope();

			while (id >= 0) {
				if (reached[id])
					break;
				reached[id] = true;
				id = dynamicScopes[id].parent();
			}
		}
		for (int j = 0; j < numScopes; j++) {
			DynamicScope scope = dynamicScopes[j];
			BitSet bitSet = scope.reachers();

			if (bitSet.get(pid) != reached[j]) {
				BitSet newBitSet = (BitSet) bitSet.clone();

				newBitSet.flip(pid);
				dynamicScopes[j] = canonic(dynamicScopes[j]
						.changeReachers(newBitSet));
			}
		}
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
	 * Push a new entry on the call stack for a process.
	 * 
	 * @param state
	 *            The old state.
	 * @param process
	 *            The pid of the process making the call.
	 * @param location
	 *            The location of the function in the new stack frame.
	 * @param lexicalScope
	 *            The lexical scope corresponding to the new dynamic scope.
	 * @param parentScope
	 *            The id of the parent dynamic scope.
	 * @return A new state that is the same as the old state with the given
	 *         process having a new entry on its call stack.
	 */
	@Override
	public State pushCallStack(State state, int pid, Function function,
			SymbolicExpression[] arguments) {
		return pushCallStack2(state, pid, function, arguments, pid);
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
	 *            "fork" command, callerPid will be different from pid and
	 *            process pid will be new and have an empty stack. Exception: if
	 *            callerPid is -1 then the new dynamic scope will have no
	 *            parent; this is used for pushing the original system function,
	 *            which has no caller
	 * @return new stack with new frame on call stack of process pid
	 */
	private State pushCallStack2(State state, int pid, Function function,
			SymbolicExpression[] arguments, int callerPid) {
		Scope containingStaticScope = function.containingScope();
		Scope functionStaticScope = function.outerScope();
		Process[] newProcesses = state.processes();
		int numScopes = state.numScopes();
		SymbolicExpression[] values;
		DynamicScope[] newScopes;
		int sid;
		int containingDynamicScopeId;
		BitSet bitSet = new BitSet(newProcesses.length);

		if (callerPid >= 0) {
			Process caller = state.process(callerPid);
			DynamicScope containingDynamicScope;

			if (caller.stackSize() == 0)
				throw new IllegalArgumentException(
						"Calling process has empty stack: " + callerPid);
			containingDynamicScopeId = caller.scope();
			while (containingDynamicScopeId >= 0) {
				containingDynamicScope = state
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
		newScopes[sid] = dynamicScope(functionStaticScope,
				containingDynamicScopeId, values, bitSet);
		{
			int id = containingDynamicScopeId;
			DynamicScope scope;

			while (id >= 0) {
				scope = newScopes[id];
				bitSet = newScopes[id].reachers();
				if (bitSet.get(pid))
					break;
				bitSet = (BitSet) bitSet.clone();
				bitSet.set(pid);
				newScopes[id] = canonic(scope.changeReachers(bitSet));
				id = scope.parent();
			}
		}
		newProcesses[pid] = canonic(state.process(pid).push(
				stackEntry(null, sid)));
		state = new State(newProcesses, newScopes, state.pathCondition());
		state = setLocation(state, pid, function.startLocation());
		state = collectScopes(state);
		return state;
	}

	@Override
	public State popCallStack(State state, int pid) {
		Process process = state.process(pid);
		Process[] processArray = state.processes();
		DynamicScope[] newScopes = state.copyScopes();

		processArray[pid] = canonic(process.pop());
		setReachablesForProc(newScopes, processArray[pid]);
		state = new State(state, processArray, newScopes, null);
		return collectScopes(state);
	}

	/**
	 * Update the path condition of a state.
	 * 
	 * @param state
	 *            The old state.
	 * @param pathCondition
	 *            The new path condition.
	 * @return A new state that is the same as the old state but with the new
	 *         path condition.
	 */
	@Override
	public State setPathCondition(State state, SymbolicExpression pathCondition) {
		return new State(state, pathCondition);
	}

}
