package edu.udel.cis.vsl.civl.state.trans;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.Map;

import edu.udel.cis.vsl.civl.err.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.state.IF.DynamicScope;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.state.trans.TransientState.DyscopeNode;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * An implementation of StateFactory based on the Transient Pattern.
 * 
 * A transient state begins in a mutable state, and become immutable upon
 * commit. Only the intrinsic data are guaranteed immutable; the extrinsic data
 * may still be mutable. In particular there are fields "seen" and "onStack"
 * which can always be set/get, regardless of the mutable bit.
 * 
 * 
 * @author Timothy K. Zirkel (zirkel)
 * @author Timothy J. McClory (tmcclory)
 * @author Stephen F. Siegel (siegel)
 */
public class TransientStateFactory implements StateFactory {

	// *************************** Fields *****************************

	private ModelFactory modelFactory;

	private SymbolicUniverse universe;

	private int numStatesSaved = 0;

	private Map<TransientObject, TransientObject> canonicMap = new HashMap<>(
			1000000);

	private Reasoner trueReasoner;

	private BooleanExpression trueExpression;

	private BooleanExpression falseExpression;

	private SymbolicExpression nullExpression;

	private long initialNumStateInstances = TransientState.instanceCount;

	// *************************** Constructors ***********************

	/**
	 * Factory to create all state objects.
	 */
	public TransientStateFactory(ModelFactory modelFactory) {
		this.modelFactory = modelFactory;
		this.universe = modelFactory.universe();
		this.trueExpression = universe.trueExpression();
		this.falseExpression = universe.falseExpression();
		this.nullExpression = universe.nullExpression();
		this.trueReasoner = universe.reasoner(trueExpression);
	}

	// ************************* Helper Methods ***********************

	private SymbolicExpression[] initialValues(Scope lexicalScope,
			int dynamicScopeId) {
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
	private TransientState pushCallStack2(TransientState state, int pid,
			CIVLFunction function, SymbolicExpression[] arguments, int callerPid) {
		TransientState theState = (TransientState) state;
		Scope containingStaticScope = function.containingScope();
		Scope functionStaticScope = function.outerScope();
		int numScopes = state.numScopes();
		SymbolicExpression[] values;
		int sid;
		int containingDynamicScopeId;
		BitSet bitSet = new BitSet(state.numProcs());

		if (callerPid >= 0) {
			ProcessState caller = theState.getProcessState(callerPid);
			DynamicScope containingDynamicScope;

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
		sid = numScopes;
		values = initialValues(functionStaticScope, sid);
		for (int i = 0; i < arguments.length; i++)
			if (arguments[i] != null)
				values[i] = arguments[i];
		bitSet.set(pid);
		// containingDynamicScopeId is the parent of new scope...
		theState = theState.addScope(new TransientDynamicScope(
				functionStaticScope, values), containingDynamicScopeId, bitSet);
		// pid can now reach all ancestors of the new scope:
		for (int id = containingDynamicScopeId; id >= 0; id = theState
				.getParentId(id)) {
			if (theState.reachableByProcess(id, pid))
				break;
			theState = theState.setReachable(pid, id, true);
		}
		theState = theState.push(pid, new TransientStackEntry(null, sid));
		// need to do this because the scopes need to be created
		// because the start location is not necessarily in the outermost
		// scope of the function:
		theState = setLocation(theState, pid, function.startLocation());
		return theState;
	}

	private boolean nsat(BooleanExpression p) {
		return trueReasoner.isValid(universe.not(p));
	}

	private TransientState collectScopesWork(State state) {
		TransientState theState = (TransientState) state;

		theState = theState.collectScopes(modelFactory);
		return theState;
	}

	// *********************** Exported Methods ***********************

	@Override
	public long getNumStateInstances() {
		return TransientState.instanceCount - initialNumStateInstances;
	}

	@Override
	public int getNumStatesSaved() {
		return numStatesSaved;
	}

	@Override
	public SymbolicUniverse symbolicUniverse() {
		return universe;
	}

	@Override
	public TransientState canonic(State state) {
		TransientState theState = (TransientState) state;
		TransientState old;

		theState.commit();
		old = (TransientState) canonicMap.get(theState);
		if (old == null) {
			theState.canonize(numStatesSaved, canonicMap, universe);
			canonicMap.put(theState, theState);
			numStatesSaved++;
			return theState;
		}
		return old;
	}

	@Override
	public TransientState initialState(Model model) {
		TransientState theState = new TransientState(
				new ArrayList<ProcessState>(), new ArrayList<DyscopeNode>(),
				trueExpression);
		CIVLFunction function = model.system();
		int numArgs = function.parameters().size();
		SymbolicExpression[] arguments = new SymbolicExpression[numArgs];

		// TODO: how to initialize the arguments to system function?
		theState = addProcess(theState, function, arguments, -1);
		theState = canonic(theState);
		return theState;
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
	public TransientState setVariable(State state, Variable variable, int pid,
			SymbolicExpression value) {
		TransientState theState = (TransientState) state;
		int scopeId = state.getScopeId(pid, variable);

		theState = setVariable(state, variable.vid(), scopeId, value);
		return theState;
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
	 * @param value
	 *            The new value of the dynamic variable.
	 * @return A new state that is the old state modified by updating the value
	 *         of the variable.
	 */
	@Override
	public TransientState setVariable(State state, int vid, int scopeId,
			SymbolicExpression value) {
		TransientState theState = (TransientState) state;

		theState = theState.setVariable(vid, scopeId, value);
		return theState;
	}

	@Override
	public TransientState addProcess(State state, CIVLFunction function,
			SymbolicExpression[] arguments, int callerPid) {
		TransientState theState = (TransientState) state;
		int numProcs = state.numProcs();
		ProcessState newProcess = new TransientProcessState(numProcs);

		theState = theState.setProcessState(numProcs, newProcess);
		theState = pushCallStack2(theState, numProcs, function, arguments,
				callerPid);
		theState = collectScopesWork(theState);
		return theState;
	}

	@Override
	public TransientState removeProcess(State state, int pid) {
		TransientState theState = (TransientState) state;

		theState = theState.removeProcessState(pid, modelFactory);
		theState = collectScopesWork(theState);
		return theState;
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
	 * </ol>
	 * 
	 * @param state
	 * @param pid
	 * @param location
	 * @return
	 */
	@Override
	public TransientState setLocation(State state, int pid, Location location) {
		TransientState theState = (TransientState) state;
		ProcessState processState = theState.getProcessState(pid);
		int dynamicScopeId = processState.getDyscopeId(); // for top of stack
		DynamicScope dynamicScope = theState.getScope(dynamicScopeId);
		Scope ss0 = dynamicScope.lexicalScope();
		Scope ss1 = location.scope();

		if (ss0 == ss1) {
			theState = theState.setLocation(pid, location);
		} else {
			Scope[] joinSequence = joinSequence(ss0, ss1);
			Scope join = joinSequence[0];

			// iterate UP...
			while (dynamicScope.lexicalScope() != join) {
				// dynamicScope is now not reachable by the top frame
				// of the call stack, and cannot be reached by any
				// other frame of the call stack (since control must
				// stay inside one function except for calls), so
				// it is no longer reachable by process pid:
				theState = theState.setReachable(pid, dynamicScopeId, false);
				dynamicScopeId = theState.getParentId(dynamicScopeId);
				if (dynamicScopeId < 0)
					throw new CIVLInternalException("State is inconsistent",
							location);
				dynamicScope = theState.getScope(dynamicScopeId);
			}
			assert dynamicScope.lexicalScope() == join;
			// iterate DOWN, adding new dynamic scopes...
			for (int i = 1; i < joinSequence.length; i++) {
				DynamicScope scope = new TransientDynamicScope(joinSequence[i],
						nullExpression);
				BitSet reachers = new BitSet();

				// only this process can reach the new dyscope:
				reachers.set(pid);
				theState = theState.addScope(scope, dynamicScopeId, reachers);
				dynamicScopeId = theState.numScopes() - 1;
			}
			theState = theState.replaceTop(pid, new TransientStackEntry(
					location, dynamicScopeId));
			theState = collectScopesWork(theState);
		}
		return theState;
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
	public TransientState pushCallStack(State state, int pid,
			CIVLFunction function, SymbolicExpression[] arguments) {
		TransientState theState = (TransientState) state;

		theState = pushCallStack2(theState, pid, function, arguments, pid);
		return theState;
	}

	/**
	 * Pops the call stack of the specified process.
	 * 
	 * Here is a FACT: let d be the dyscope pointed to by the top activation
	 * frame A of p's call stack. Let f be the function to which d belongs. Let
	 * D be the set of dyscopes consisting of d and the ancestors of d up to and
	 * including the dyscope whose corresponding static scope is the function
	 * node for f. These are all the dyscopes involved in the call to f. Now
	 * here is the FACT: A is the only frame on p's call stack which can reach a
	 * dyscope in D. (Other processes, e.g., those spawned by p, may be able to
	 * reach those dyscopes, but not p.) Hence when p is popped, p can no longer
	 * reach any of the dyscopes in D. 
	 * 
	 * Its ability to reach all other dyscopes is not affected.
	 * TODO: WRONG: it also may not be able to reach other scopes.
	 * Think of the last frame to be popped from the stack.
	 * 
	 */
	@Override
	public TransientState popCallStack(State state, int pid) {
		TransientState theState = (TransientState) state;
		ProcessState processState = theState.getProcessState(pid);
		int dyscopeId = processState.getDyscopeId();
		DynamicScope scope = theState.getScope(dyscopeId);
		Scope staticScope = scope.lexicalScope();
		CIVLFunction function = staticScope.function();
		Scope functionScope = function.outerScope();

		while (true) {
			theState = theState.setReachable(pid, dyscopeId, false);
			if (staticScope == functionScope)
				break;
			dyscopeId = theState.getParentId(dyscopeId);
			if (dyscopeId < 0)
				break;
			staticScope = staticScope.parent();
		}
		theState = theState.pop(pid);
		theState = collectScopesWork(theState);
		return theState;
	}

	@Override
	public State simplify(State state) {
		TransientState theState = (TransientState) state;
		int numScopes = theState.numScopes();
		Reasoner reasoner = universe.reasoner(theState.getPathCondition());
		BooleanExpression newPathCondition = reasoner.getReducedContext();

		if (nsat(newPathCondition)) {
			theState = theState.setPathCondition(falseExpression);
		} else {
			theState = theState.setPathCondition(newPathCondition);
			for (int i = 0; i < numScopes; i++) {
				DynamicScope oldScope = theState.getScope(i);
				int numVars = oldScope.lexicalScope().numVariables();

				for (int j = 0; j < numVars; j++) {
					SymbolicExpression oldValue = oldScope.getValue(j);
					SymbolicExpression newValue = reasoner.simplify(oldValue);

					if (oldValue != newValue)
						theState = theState.setVariable(j, i, newValue);
				}
			}
		}
		return theState;
	}

	/**
	 * Nothing to do, since this factory is already collecting scopes after any
	 * operation that could possible change the scopes.
	 */
	@Override
	public TransientState collectScopes(State state) {
		return (TransientState) state;
	}

	@Override
	public boolean lockedByAtomic(State state) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public ProcessState processInAtomic(State state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public State getAtomicLock(State state, int pid) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public State releaseAtomicLock(State state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public State setProcessState(State state, ProcessState p, int pid) {
		// TODO Auto-generated method stub
		return null;
	}

}
