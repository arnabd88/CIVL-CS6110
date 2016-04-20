package edu.udel.cis.vsl.civl.state.immutable;

import java.io.PrintStream;
import java.util.BitSet;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import edu.udel.cis.vsl.civl.err.CIVLExecutionException.Certainty;
import edu.udel.cis.vsl.civl.err.CIVLExecutionException.ErrorKind;
import edu.udel.cis.vsl.civl.err.CIVLInternalException;
import edu.udel.cis.vsl.civl.err.CIVLStateException;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLHeapType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLStructOrUnionType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.type.StructOrUnionField;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.run.UserInterface;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.StackEntry;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.util.Pair;
import edu.udel.cis.vsl.civl.util.Triple;
import edu.udel.cis.vsl.gmc.GMCConfiguration;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.ArrayElementReference;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.expr.TupleComponentReference;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject.SymbolicObjectKind;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicSequence;

/**
 * An implementation of StateFactory based on the Immutable Pattern.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * @author Timothy J. McClory (tmcclory)
 * @author Stephen F. Siegel (siegel)
 * 
 */
public class ImmutableStateFactory implements StateFactory {

	/* *************************** Static Fields *************************** */

	private static String HEAP_VARIABLE = "__heap";

	/* ************************** Instance Fields ************************** */

	private GMCConfiguration config;

	private boolean simplify;

	private long initialNumStateInstances = ImmutableState.instanceCount;

	private ModelFactory modelFactory;

	private Map<ImmutableProcessState, ImmutableProcessState> processMap = new HashMap<>(
			100000);

	private Map<ImmutableDynamicScope, ImmutableDynamicScope> scopeMap = new HashMap<>(
			100000);

	private int stateCount = 0;

	private int processCount = 0;

	private int dyscopeCount = 0;

	private Map<ImmutableState, ImmutableState> stateMap = new HashMap<>(
			1000000);

	private Reasoner trueReasoner;

	private SymbolicUniverse universe;

	// TODO factor out common/side-effect free methods
	private Evaluator evaluator;

	private IntObject twoObj;

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
		this.twoObj = universe.intObject(2);
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
			int parent, int parentIdentifier, int dynamicScopeId,
			BitSet reachers) {
		return new ImmutableDynamicScope(lexicalScope, parent,
				parentIdentifier, initialValues(lexicalScope, dynamicScopeId),
				reachers, this.dyscopeCount++);
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

	private String pointerValueToString(CIVLSource source, State state,
			SymbolicExpression pointer) {
		if (pointer.operator() == SymbolicOperator.NULL)
			return pointer.toString();
		else if(pointer.operator() != SymbolicOperator.CONCRETE)
			return pointer.toString();
		else {
			SymbolicTupleType pointerType = (SymbolicTupleType) pointer.type();
			
			if(!pointerType.name().getString().equalsIgnoreCase("pointer")){
				return pointer.toString();
			}
			
			int dyscopeId = evaluator.getScopeId(source, pointer);

			if (dyscopeId < 0)
				return "UNDEFINED";
			else {
				int vid = evaluator.getVariableId(source, pointer);
				ImmutableDynamicScope dyscope = (ImmutableDynamicScope) state
						.getScope(dyscopeId);
				Variable variable = dyscope.lexicalScope().variable(vid);
				String variableName = variable.name().name();
				ReferenceExpression reference = (ReferenceExpression) universe
						.tupleRead(pointer, this.twoObj);

				if (variableName.equals(HEAP_VARIABLE)) {
					String resultString = heapObjectToString(source, dyscopeId,
							variable.type(), reference).third;

					return resultString;
				} else {
					StringBuffer result = new StringBuffer();

					result.append('&');
					result.append(variable.name());
					result.append("<d");
					result.append(dyscope.identifier());
					result.append('>');
					result.append(referenceToString(source, variable.type(),
							reference).right);
					return result.toString();
				}
			}
		}
	}

	private Triple<Integer, CIVLType, String> heapObjectToString(
			CIVLSource source, int dyscopeId, CIVLType type,
			ReferenceExpression reference) {
		StringBuffer result = new StringBuffer();

		if (reference.isIdentityReference()) {
			result.append("&heapObject<d");
			result.append(dyscopeId);
			result.append(',');
			return new Triple<>(0, type, result.toString());
		} else if (reference.isArrayElementReference()) {
			ArrayElementReference arrayEleRef = (ArrayElementReference) reference;
			Triple<Integer, CIVLType, String> parentResult = heapObjectToString(
					source, dyscopeId, type, arrayEleRef.getParent());
			NumericExpression index = arrayEleRef.getIndex();

			switch (parentResult.first) {
			case 0:
				throw new CIVLInternalException("Unreachable", source);
			case 1:
				result.append(parentResult.third);
				// result.append("number of malloc calls: ");
				result.append(index);
				result.append('>');
				return new Triple<>(2, parentResult.second, result.toString());
			case 2:
				result.append(parentResult.third);
				result.append('[');
				result.append(index);
				result.append(']');
				return new Triple<>(-1, parentResult.second, result.toString());
			default:
				CIVLType arrayEleType = ((CIVLArrayType) parentResult.second)
				.elementType();
				
				result.append(parentResult.third);
				result.append('[');
				result.append(index);
				result.append(']');
				return new Triple<>(-1, arrayEleType, result.toString());
			}
		} else if (reference.isTupleComponentReference()) {
			TupleComponentReference tupleCompRef = (TupleComponentReference) reference;
			Triple<Integer, CIVLType, String> parentResult = heapObjectToString(
					source, dyscopeId, type, tupleCompRef.getParent());
			IntObject index = tupleCompRef.getIndex();

			switch (parentResult.first) {
			case 0:
				CIVLHeapType heapType = (CIVLHeapType) parentResult.second;
				int indexId = index.getInt();
				CIVLType heapObjType = heapType.getMalloc(indexId)
						.getStaticElementType();

				result.append(parentResult.third);
				// result.append("malloc id: ");
				result.append(index.getInt());
				result.append(',');
				return new Triple<>(1, heapObjType, result.toString());
			case 1:
			case 2:
				throw new CIVLInternalException("Unreachable", source);
			default:
				CIVLStructOrUnionType structOrUnionType = (CIVLStructOrUnionType) parentResult.second;
				StructOrUnionField field = structOrUnionType.getField(index
						.getInt());

				result.append(parentResult.third);
				result.append('.');
				result.append(field.name());
				return new Triple<>(-1, field.type(), result.toString());
			}
		} else {
			throw new CIVLInternalException("Unreachable", source);
		}
	}

	private Pair<CIVLType, String> referenceToString(CIVLSource source,
			CIVLType type, ReferenceExpression reference) {
		StringBuffer result = new StringBuffer();

		if (reference.isIdentityReference())
			return new Pair<>(type, result.toString());
		if (reference.isArrayElementReference()) {
			ArrayElementReference arrayEleRef = (ArrayElementReference) reference;
			Pair<CIVLType, String> parentResult = this.referenceToString(
					source, type, arrayEleRef.getParent());
			String parent = parentResult.right;
			CIVLType arrayEleType = ((CIVLArrayType) parentResult.left)
					.elementType();
			NumericExpression index = arrayEleRef.getIndex();

			result.append(parent);
			result.append('[');
			result.append(index);
			result.append(']');
			return new Pair<>(arrayEleType, result.toString());
		} else if (reference.isTupleComponentReference()) {
			TupleComponentReference tupleComponentRef = (TupleComponentReference) reference;
			IntObject index = tupleComponentRef.getIndex();
			Pair<CIVLType, String> parentResult = this.referenceToString(
					source, type, tupleComponentRef.getParent());
			String parent = parentResult.right;
			CIVLStructOrUnionType structOrUnionType = (CIVLStructOrUnionType) parentResult.left;
			StructOrUnionField field = structOrUnionType.getField(index
					.getInt());

			result.append(parent);
			result.append('.');
			result.append(field.name());
			return new Pair<CIVLType, String>(field.type(), result.toString());
		} else {
			throw new CIVLInternalException("Unreachable", source);
		}
	}

	private void printDynamicScope(PrintStream out, State state,
			ImmutableDynamicScope dyscope, String id, String prefix) {
		Scope lexicalScope = dyscope.lexicalScope();
		int numVars = lexicalScope.numVariables();
		BitSet reachers = dyscope.getReachers();
		int bitSetLength = reachers.length();
		boolean first = true;

		out.println(prefix + "dyscope d" + dyscope.identifier() + " (id=" + id
				+ ", parent=d" + dyscope.getParentIdentifier() + ", static="
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
				out.println(pointerValueToString(variable.getSource(), state,
						value));
			} else
				out.println(value);
		}
		out.flush();
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
		int containingDynamicScopeId, containingDynamicScopeIdentifier;
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

			for (Variable variable : procrefVariableIter) {
				int vid = variable.vid();
				SymbolicExpression oldValue = dynamicScope.getValue(vid);
				SymbolicExpression newValue = universe.substitute(oldValue,
						procSubMap);

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
							dynamicScope.getParent(),
							dynamicScope.getParentIdentifier(), newValues,
							newBitSet, dynamicScope.identifier());
			} else if (newScopes != null) {
				newScopes[i] = dynamicScope;
			}
		}
		return newScopes;
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

	/**
	 * Checks if a heap is null or empty.
	 * 
	 * @param heapValue
	 *            The value of the heap to be checked.
	 * @return True iff the heap has null value or is empty.
	 */
	private boolean isEmptyHeap(SymbolicExpression heapValue) {
		if (heapValue.isNull())
			return true;
		else {
			SymbolicSequence<?> heapFields = (SymbolicSequence<?>) heapValue
					.argument(0);
			int count = heapFields.size();

			for (int i = 0; i < count; i++) {
				SymbolicExpression heapField = heapFields.get(i);
				SymbolicSequence<?> heapFieldObjets = (SymbolicSequence<?>) heapField
						.argument(0);
				int size = heapFieldObjets.size();

				for (int j = 0; j < size; j++) {
					SymbolicExpression heapFieldObj = heapFieldObjets.get(j);
					SymbolicObject heapFieldObjValue = heapFieldObj.argument(0);

					if (heapFieldObjValue.symbolicObjectKind() == SymbolicObjectKind.STRING) {
						String value = ((StringObject) heapFieldObjValue)
								.getString();

						if (value.equals("UNDEFINED"))
							continue;
					}
					return false;
				}
			}
		}
		return true;
	}

	/* ********************** Methods from StateFactory ******************** */

	@Override
	public ImmutableState addProcess(State state, CIVLFunction function,
			SymbolicExpression[] arguments, int callerPid) {
		ImmutableState theState = (ImmutableState) state;
		int numProcs = theState.numProcs();
		ImmutableProcessState[] newProcesses;

		newProcesses = theState.copyAndExpandProcesses();
		newProcesses[numProcs] = new ImmutableProcessState(numProcs,
				this.processCount++);
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
		if (simplify) {
			ImmutableState simplifiedState = theState.simplifiedState;

			if (simplifiedState == null) {
				simplifiedState = simplify(theState);
				simplifiedState = flyweight(simplifiedState);
				theState.simplifiedState = simplifiedState;
				simplifiedState.simplifiedState = simplifiedState;
				return simplifiedState;
			}
		}
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
			if (id < 0) {
				ImmutableDynamicScope scopeToBeRemoved = theState.getScope(i);
				Variable heapVariable = scopeToBeRemoved.lexicalScope()
						.variable("__heap");
				SymbolicExpression heapValue = scopeToBeRemoved
						.getValue(heapVariable.vid());

				if (!this.isEmptyHeap(heapValue)) {
					throw new CIVLStateException(ErrorKind.MEMORY_LEAK,
							Certainty.CONCRETE, "The unreachable dyscope "
									+ scopeToBeRemoved.identifier() + "(scope<"
									+ i + ">)" + " has a non-empty heap "
									+ heapValue.toString() + ".", state, this,
							heapVariable.getSource());
				}
			}
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
					int oldParentIdentifier = oldScope.identifier();

					newScopes[newId] = oldScope.updateDyscopeIds(scopeSubMap,
							universe, oldParent < 0 ? oldParent
									: oldToNew[oldParent], oldParentIdentifier);
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
	public void printState(PrintStream out, State state) {
		int numScopes = state.numScopes();
		int numProcs = state.numProcs();

		out.print("State " + state.identifier());
		out.println();
		out.println("| Path condition");
		out.println("| | " + state.getPathCondition());
		out.println("| Dynamic scopes");
		for (int i = 0; i < numScopes; i++) {
			ImmutableDynamicScope dyscope = (ImmutableDynamicScope) state
					.getScope(i);

			if (dyscope == null)
				out.println("| | dyscope - (id=" + i + "): null");
			else
				printDynamicScope(out, state, dyscope, "" + i, "| | ");
			// dyscope.print(out, "" + i, "| | ");
		}
		out.println("| Process states");
		for (int pid = 0; pid < numProcs; pid++) {
			ProcessState process = state.getProcessState(pid);

			if (process == null)
				out.println("| | process - (id=" + pid + "): null");
			else
				process.print(out, "| | ");
		}
		out.flush();
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
		return this.setVariable(state, 0, 0, modelFactory.processValue(-1));
	}

	@Override
	public void setEvaluator(Evaluator evaluator) {
		this.evaluator = evaluator;
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
		int dynamicScopeIdentifier = dynamicScope.identifier();
		Scope ss0 = dynamicScope.lexicalScope();
		Scope ss1 = location.scope();

		if (ss0 == ss1) {
			processArray[pid] = theState.getProcessState(pid)
					.replaceTop(
							stackEntry(location, dynamicScopeId,
									dynamicScopeIdentifier));
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
				dynamicScopeIdentifier = dynamicScope.identifier();
			}
			if (joinSequence.length == 1) {
				processArray[pid] = theState.getProcessState(pid).replaceTop(
						stackEntry(location, dynamicScopeId,
								dynamicScopeIdentifier));
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
							dynamicScopeId, dynamicScopeIdentifier, index,
							reachers);
					dynamicScopeId = index;
					index++;
				}
				process = process
						.replaceTop(stackEntry(location, dynamicScopeId,
								newScopes[dynamicScopeId].identifier()));
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
				oldScope.getParent(), oldScope.getParentIdentifier(),
				newValues, oldScope.getReachers(), oldScope.identifier());
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
	public ImmutableState simplify(State state) {
		ImmutableState theState = (ImmutableState) state;

		if (theState.simplifiedState != null)
			return theState.simplifiedState;
		else {
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
	}

	@Override
	public SymbolicUniverse symbolicUniverse() {
		return universe;
	}

	/* ************************ Other public methods *********************** */

	public GMCConfiguration getConfiguration() {
		return config;
	}

	@Override
	public boolean isDesendantOf(State state, int ancestor, int descendant) {
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
	public int lowestCommonAncestor(State state, int one, int another) {
		if (one == another) {
			return one;
		} else {
			int parent = one;

			while (parent >= 0) {
				if (parent == another
						|| this.isDesendantOf(state, parent, another))
					return parent;
				parent = state.getParentId(parent);
			}
		}
		return state.rootScopeID();
	}

	// @Override
	// public int getScopeId(State state, int pid, Variable variable){
	// return state.getScopeId(pid, variable);
	// }

}
