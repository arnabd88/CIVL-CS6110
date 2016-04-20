package edu.udel.cis.vsl.civl.state.persistent;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

import com.github.krukow.clj_ds.PersistentVector;

import edu.udel.cis.vsl.civl.err.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

public class PersistentStateFactory implements StateFactory {

	// *************************** Fields *****************************

	private ModelFactory modelFactory;

	private int stateCount = 0;

	private SymbolicUniverse universe;

	private Map<PersistentObject, PersistentObject> canonicMap = new HashMap<>(
			1000000);

	private Reasoner trueReasoner;

	private long initialNumStateInstances = PersistentState.getInstanceCount();

	private SymbolicExpression nullExpression;

	private BooleanExpression trueExpression;

	private BooleanExpression falseExpression;

	// *************************** Constructors ***********************

	/**
	 * Factory to create all state objects.
	 */
	public PersistentStateFactory(ModelFactory modelFactory) {
		this.modelFactory = modelFactory;
		this.universe = modelFactory.universe();
		this.trueReasoner = universe.reasoner(universe.trueExpression());
		this.nullExpression = universe.nullExpression();
		this.trueExpression = universe.trueExpression();
		this.falseExpression = universe.falseExpression();

	}

	// ************************* Helper Methods ***********************

	@SuppressWarnings("unchecked")
	private <T extends PersistentObject> T canonicObj(T obj) {
		return (T) obj.canonize(universe, canonicMap);
		// note special handling for state since we are adding
		// canonic ID.
	}

	private ArrayList<ValueVector> initialVectors = new ArrayList<>();

	private ValueVector initialValues(Scope lexicalScope, int dynamicScopeId) {
		int numVars = lexicalScope.numVariables();
		ValueVector vector;

		while (numVars >= initialVectors.size())
			initialVectors.add(null);
		vector = initialVectors.get(numVars);
		if (vector == null) {
			vector = new ValueVector(nullExpression, numVars);
			vector = canonicObj(vector);
			initialVectors.set(numVars, vector);
		}
		return vector;
	}

	/**
	 * A dynamic scope.
	 * 
	 * @param lexicalScope
	 *            The lexical scope corresponding to this dynamic scope.
	 * @param parent
	 *            The parent of this dynamic scope. -1 only for the topmost
	 *            dynamic scope.
	 * @param dynamicScopeId
	 *            id for new scope
	 * @param reachers
	 *            set of processes which can reach the new scope
	 * @return A new dynamic scope.
	 */
	private PersistentDynamicScope initialDynamicScope(Scope lexicalScope,
			int parent, int dynamicScopeId, IntSet reachers) {
		return new PersistentDynamicScope(lexicalScope, parent, initialValues(
				lexicalScope, dynamicScopeId), reachers);
	}

	/**
	 * Given two static scopes, this method computes a non-empty sequence of
	 * scopes with the following properties:
	 * <ul>
	 * <li>The first (0-th) element of the sequence is the join of scope1 and
	 * scope2.</li>
	 * <li>The last element is scope2.</li>
	 * <li>For each i (0<=i&lt;length-1), the i-th element is the parent of the
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
	 * @return state with new frame on call stack of process pid
	 */
	private PersistentState pushCallStack2(PersistentState state, int pid,
			CIVLFunction function, SymbolicExpression[] arguments, int callerPid) {
		PersistentState theState = (PersistentState) state;
		int numScopes = theState.numScopes();
		int sid = numScopes;
		ProcStateVector procVector = theState.getProcStateVector().push(pid,
				new PersistentStackEntry(null, sid));
		PersistentVector<PersistentDynamicScope> scopeVector = theState
				.getScopeTree().getValues();
		Scope containingStaticScope = function.containingScope();
		Scope functionStaticScope = function.outerScope();
		PersistentVector<SymbolicExpression> values = initialValues(
				functionStaticScope, sid).getValues();
		int containingDynamicScopeId;

		if (callerPid >= 0) {
			PersistentProcessState caller = theState.getProcessState(callerPid);
			PersistentDynamicScope containingDynamicScope;

			if (caller.stackSize() == 0)
				throw new CIVLInternalException(
						"Calling process has empty stack: " + callerPid,
						function);
			containingDynamicScopeId = caller.getDyscopeId();
			while (containingDynamicScopeId >= 0) {
				containingDynamicScope = theState
						.getScope(containingDynamicScopeId);
				if (containingStaticScope == containingDynamicScope
						.lexicalScope())
					break;
				containingDynamicScopeId = containingDynamicScope.getParent();
			}
			if (containingDynamicScopeId < 0)
				throw new IllegalArgumentException(
						"Called function not visible:\nfunction: " + function
								+ "\npid: " + pid + "\ncallerPid:" + callerPid
								+ "\narguments: " + arguments);
		} else {
			containingDynamicScopeId = -1;
		}
		for (int i = 0; i < arguments.length; i++) {
			SymbolicExpression arg = arguments[i];

			if (arg != null)
				values = values.plusN(i, arg);
		}
		// add a dyscope under containingDynamicScope:
		scopeVector = scopeVector.plus(new PersistentDynamicScope(
				functionStaticScope, containingDynamicScopeId, new ValueVector(
						values), IntSet.singleton(pid)));
		// pid can now reach all ancestors of the new scope:
		for (int id = containingDynamicScopeId; id >= 0;) {
			PersistentDynamicScope scope = scopeVector.get(id);
			PersistentDynamicScope newScope = scope.setReachable(pid);

			if (scope == newScope)
				break;
			scopeVector = scopeVector.plusN(id, newScope);
			id = scope.getParent();
		}
		theState = new PersistentState(procVector,
				new DyscopeTree(scopeVector), theState.getPathCondition());
		// new scopes may need to be created because the start location
		// is not necessarily in the outermost scope of the function:
		theState = setLocation(theState, pid, function.startLocation());
		theState = theState.collectScopes(modelFactory);
		return theState;
	}

	private boolean nsat(BooleanExpression p) {
		return trueReasoner.isValid(universe.not(p));
	}

	private PersistentState collectScopesWork(State state) {
		PersistentState theState = (PersistentState) state;

		theState = theState.collectScopes(modelFactory);
		return theState;
	}

	/****************** Methods from StateFactory ********************/

	@Override
	public SymbolicUniverse symbolicUniverse() {
		return universe;
	}

	@Override
	public PersistentState canonic(State state) {
		PersistentState result = canonicObj((PersistentState) state);

		if (result.getCanonicId() < 0) {
			result.setCanonicId(stateCount);
			stateCount++;
		}
		return result;
	}

	@Override
	public PersistentState initialState(Model model) {
		PersistentState state = new PersistentState(new ProcStateVector(),
				new DyscopeTree(), trueExpression);
		CIVLFunction function = model.system();
		int numArgs = function.parameters().size();
		SymbolicExpression[] arguments = new SymbolicExpression[numArgs];

		// TODO: how to initialize the arguments to system function?
		state = addProcess(state, function, arguments, -1);
		state = this.setVariable(state, 0, 0, modelFactory.processValue(-1));
		return canonic(state);
	}

	@Override
	public PersistentState setVariable(State state, Variable variable, int pid,
			SymbolicExpression value) {
		PersistentState theState = (PersistentState) state;
		int scopeId = state.getScopeId(pid, variable);

		theState = theState.setVariable(variable.vid(), scopeId, value);
		return theState;
	}

	@Override
	public PersistentState setVariable(State state, int vid, int scopeId,
			SymbolicExpression value) {
		PersistentState theState = (PersistentState) state;

		theState = theState.setVariable(vid, scopeId, value);
		return theState;
	}

	@Override
	public PersistentState addProcess(State state, CIVLFunction function,
			SymbolicExpression[] arguments, int callerPid) {
		PersistentState theState = (PersistentState) state;
		int numProcs = state.numProcs();
		PersistentProcessState newProcess = new PersistentProcessState(numProcs);

		theState = theState.addProcessState(newProcess);
		theState = pushCallStack2(theState, numProcs, function, arguments,
				callerPid);
		theState = collectScopesWork(theState);
		return theState;
	}

	@Override
	public PersistentState removeProcess(State state, int pid) {
		PersistentState theState = (PersistentState) state;

		theState = theState.removeProcessState(pid, modelFactory);
		return theState;
	}

	@Override
	public PersistentState setLocation(State state, int pid, Location location) {
		PersistentState theState = (PersistentState) state;
		ProcStateVector procVector = theState.getProcStateVector();
		PersistentProcessState processState = procVector.get(pid);
		int dynamicScopeId = processState.getDyscopeId(); // for top of stack
		DyscopeTree scopeTree = theState.getScopeTree();
		PersistentVector<PersistentDynamicScope> scopeVector = scopeTree.values;
		PersistentDynamicScope dynamicScope = scopeVector.get(dynamicScopeId);
		Scope ss0 = dynamicScope.lexicalScope();
		Scope ss1 = location.scope();

		if (ss0 == ss1) {
			theState = theState.setLocation(pid, location);
		} else {
			Scope[] joinSequence = joinSequence(ss0, ss1);
			Scope join = joinSequence[0];
			int numScopes = scopeVector.size();

			// iterate UP...
			while (dynamicScope.lexicalScope() != join) {
				// dynamicScope is now not reachable by the top frame
				// of the call stack, and cannot be reached by any
				// other frame of the call stack (since control must
				// stay inside one function except for calls), so
				// it is no longer reachable by process pid:
				PersistentDynamicScope newScope = dynamicScope
						.unsetReachable(pid);

				if (newScope != dynamicScope)
					scopeVector = scopeVector.plusN(dynamicScopeId, newScope);
				dynamicScopeId = dynamicScope.getParent();
				if (dynamicScopeId < 0)
					throw new CIVLInternalException("State is inconsistent",
							location);
				dynamicScope = scopeVector.get(dynamicScopeId);
			}
			assert dynamicScope.lexicalScope() == join;
			// iterate DOWN, adding new dynamic scopes...
			for (int i = 1; i < joinSequence.length; i++) {
				PersistentDynamicScope newScope = initialDynamicScope(
						joinSequence[i], dynamicScopeId, numScopes,
						IntSet.singleton(pid));

				scopeVector = scopeVector.plus(newScope);
				dynamicScopeId = numScopes;
				numScopes++;
			}
			scopeTree = new DyscopeTree(scopeVector);
			processState = processState.replaceTop(new PersistentStackEntry(
					location, dynamicScopeId));
			procVector = (ProcStateVector) procVector.set(pid, processState);
			theState = new PersistentState(procVector, scopeTree,
					theState.getPathCondition());
			theState = collectScopesWork(theState);
		}
		return theState;
	}

	@Override
	public PersistentState pushCallStack(State state, int pid,
			CIVLFunction function, SymbolicExpression[] arguments) {
		PersistentState theState = (PersistentState) state;

		theState = pushCallStack2(theState, pid, function, arguments, pid);
		return theState;
	}

	@Override
	public PersistentState popCallStack(State state, int pid) {
		PersistentState theState = (PersistentState) state;
		ProcStateVector procVector = theState.getProcStateVector();
		PersistentProcessState processState = procVector.get(pid);
		int dyscopeId = processState.getDyscopeId();
		DyscopeTree scopeTree = theState.getScopeTree();
		PersistentVector<PersistentDynamicScope> scopeVector = scopeTree
				.getValues();
		PersistentDynamicScope scope = scopeVector.get(dyscopeId);
		Scope staticScope = scope.lexicalScope();
		CIVLFunction function = staticScope.function();
		Scope functionScope = function.outerScope();
		boolean staying = processState.getCallStack().size() > 1;

		while (true) {
			PersistentDynamicScope newScope = scope.unsetReachable(pid);

			if (newScope != scope)
				scopeVector = scopeVector.plusN(dyscopeId, newScope);
			if (staying && staticScope == functionScope)
				break;
			dyscopeId = scope.getParent();
			if (dyscopeId < 0)
				break;
			scope = scopeVector.get(dyscopeId);
			staticScope = scope.lexicalScope();
		}
		scopeTree = new DyscopeTree(scopeVector);
		processState = processState.pop();
		procVector = (ProcStateVector) procVector.set(pid, processState);
		theState = new PersistentState(procVector, scopeTree,
				theState.getPathCondition());
		theState = collectScopesWork(theState);
		return theState;
	}

	@Override
	public PersistentState simplify(State state) {
		PersistentState theState = (PersistentState) state;
		BooleanExpression pathCondition = theState.getPathCondition();
		Reasoner reasoner = universe.reasoner(pathCondition);
		BooleanExpression newPathCondition = reasoner.getReducedContext();

		if (nsat(newPathCondition)) {
			theState = theState.setPathCondition(falseExpression);
		} else {
			DyscopeTree oldScopeTree = theState.getScopeTree();
			DyscopeTree newScopeTree = oldScopeTree.simplify(reasoner);

			if (newPathCondition != pathCondition
					|| oldScopeTree != newScopeTree)
				theState = new PersistentState(theState.getProcStateVector(),
						newScopeTree, newPathCondition);
		}
		return theState;
	}

	@Override
	public long getNumStateInstances() {
		return PersistentState.getInstanceCount() - initialNumStateInstances;
	}

	@Override
	public int getNumStatesSaved() {
		return stateCount;
	}

	@Override
	public PersistentState collectScopes(State state) {
		return (PersistentState) state;
	}

	@Override
	public boolean lockedByAtomic(State state) {
		SymbolicExpression symbolicAtomicPid = state.getVariableValue(0, 0);
		int atomicPid = modelFactory.getProcessId(modelFactory.systemSource(),
				symbolicAtomicPid);

		return atomicPid >= 0;
	}

	@Override
	public PersistentProcessState processInAtomic(State state) {
		PersistentState theState = (PersistentState) state;
		SymbolicExpression symbolicAtomicPid = theState.getVariableValue(0, 0);
		int atomicPid = modelFactory.getProcessId(modelFactory.systemSource(),
				symbolicAtomicPid);

		if (atomicPid < 0)
			return null;
		return theState.getProcessState(atomicPid);
	}

	@Override
	public PersistentState getAtomicLock(State state, int pid) {
		return this.setVariable(state, 0, 0, modelFactory.processValue(pid));
	}

	@Override
	public PersistentState releaseAtomicLock(State state) {
		return this.setVariable(state, 0, 0, modelFactory.processValue(-1));
	}

	@Override
	public PersistentState setProcessState(State state, ProcessState p, int pid) {
		PersistentState theState = (PersistentState) state;
		ProcStateVector oldProcVector = theState.getProcStateVector();
		ProcStateVector newProcVector = (ProcStateVector) oldProcVector.set(
				pid, (PersistentProcessState) p);

		return oldProcVector == newProcVector ? theState : new PersistentState(
				newProcVector, theState.getScopeTree(),
				theState.getPathCondition());
	}

}
