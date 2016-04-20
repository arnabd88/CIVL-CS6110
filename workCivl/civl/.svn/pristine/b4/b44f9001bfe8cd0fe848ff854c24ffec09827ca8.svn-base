package edu.udel.cis.vsl.civl.kripke;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Stack;

import edu.udel.cis.vsl.civl.library.IF.LibraryLoader;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.statement.WaitStatement;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.transition.Transition;
import edu.udel.cis.vsl.civl.transition.TransitionFactory;
import edu.udel.cis.vsl.civl.transition.TransitionSequence;
import edu.udel.cis.vsl.civl.util.Pair;
import edu.udel.cis.vsl.gmc.EnablerIF;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;

/**
 * Enabler implements {@link EnablerIF} for CIVL models. Its basic functionality
 * is to obtain the set of enabled transitions of a certain state. Currently,
 * there are two partial order reduction algorithms in Enabler, namely standard
 * POR ({@link #enabledTransitionsScope1(State)}) and scoped POR (
 * {@link #enabledTransitionsScope2(State)}). By default, the standard POR is
 * used.
 * 
 * @author Manchun Zheng (zmanchun)
 * @author Timothy K. Zirkel (zirkel)
 */
public class ScopedEnabler extends Enabler implements
		EnablerIF<State, Transition, TransitionSequence> {

	/* *************************** Instance Fields ************************* */

	/**
	 * The number of ample sets, initialized as 0.
	 */
	private long ampleSets = 0;

	/**
	 * The number of enabled
	 */
	private long enabledTransitionSets = 0;

	/**
	 * true iff want to use the new scope POR algorithm
	 */
	public boolean scpPor = false;

	/* ***************************** Constructors ************************** */

	/**
	 * 
	 * @param transitionFactory
	 *            The transition factory to be used in this enabler.
	 * @param evaluator
	 *            The evaluator to be used to calculate and evaluate new path
	 *            condition
	 * @param executor
	 *            The executor to be used
	 * @param sPor
	 *            True iff want to use scoped POR instead of default POR.
	 * @param showAmpleSet
	 */
	public ScopedEnabler(TransitionFactory transitionFactory,
			Evaluator evaluator, Executor executor, boolean sPor,
			boolean showAmpleSet, boolean showAmpleSetWtStates,
			LibraryLoader libLoader) {
		super(transitionFactory, evaluator, executor, showAmpleSet,
				showAmpleSetWtStates, libLoader);
		this.scpPor = sPor;
		if (this.scpPor)
			this.debugOut.println("scoped POR is enabled.");
	}

	/* ************************ Methods from Enabler ********************* */

	@Override
	protected TransitionSequence enabledTransitionsPOR(State state) {
		TransitionSequence transitions;

		if (!this.scpPor) {
			if (debugging && enabledTransitionSets % 1000 == 0) {
				System.out.println("Ample transition sets: " + ampleSets + "/"
						+ enabledTransitionSets);
			}
			transitions = enabledTransitionsScope1(state);
			if (debugging) {
				if (transitions.size() > 1) {
					debugOut.println("Number of transitions at state "
							+ state.identifier() + "is " + transitions.size());
					this.stateFactory.printState(debugOut, state);
				}
			}
		} else
			transitions = enabledTransitionsScope2(state);
		return transitions;
	}

	/* *************************** Private Methods ************************* */

	/**
	 * Obtain the set of processes to generate ample set transitions TODO: try
	 * to avoid repeatedly calculating things like joinedPid, path condition
	 * satisfiability, etc.
	 * 
	 * @param state
	 *            The state to work with.
	 * @return
	 */
	private LinkedHashSet<ProcessState> ampleProcesses(State state) {
		LinkedHashSet<ProcessState> ampleProcesses = new LinkedHashSet<>();
		Stack<Integer> workingScopes = new Stack<>();
		HashSet<Integer> visitedScopes = new HashSet<>();
		HashSet<Integer> visitedProcesses = new HashSet<>();
		ArrayList<ProcessState> allProcesses = new ArrayList<>();
		int numOfProcs;
		ProcessState p;
		ArrayList<Integer> iScopesP;
		Pair<ProcessState, Integer> minimalReacher;

		for (ProcessState tmp : state.getProcessStates()) {
			if (tmp == null || tmp.hasEmptyStack())
				continue;
			allProcesses.add(tmp);
		}
		if (allProcesses.isEmpty())
			return ampleProcesses;
		numOfProcs = allProcesses.size();
		minimalReacher = minimalReachers(state, allProcesses);
		if (minimalReacher == null)
			return ampleProcesses;
		if (minimalReacher.right == 1) {
			ampleProcesses.add(minimalReacher.left);
			return ampleProcesses;
		}
		// If the minimal number of reachers equals to the number of processes
		// return all processes as the ample set immediately
		if (minimalReacher.right == numOfProcs) {
			ampleProcesses.addAll(allProcesses);
			return ampleProcesses;
		}
		// Start from p, whose impact factor has the least number of reachers
		p = minimalReacher.left;
		ampleProcesses.add(p);
		iScopesP = impactScopesOfProcess(p, state);
		// Push into the working stack the impact scopes of all possible
		// statements of process
		for (Integer delta : iScopesP) {
			workingScopes.push(delta);
		}
		// Generate reacher processes of each dyscope in workingScope (impact
		// scope stack) the impact scopes of new processes are added to
		// workingScope if a wait process is encountered, the process it waits
		// for is considered pointer is considered to be "root" scope
		while (!workingScopes.isEmpty()) {
			int impactScope = workingScopes.pop();
			ArrayList<ProcessState> reachersOfImpactScope;
			ArrayList<ProcessState> waitDepedentProcesses;

			// If imScope is a descendant of some dyscope in visitedScopes, all
			// its owner processes are all in ampleProcesses already, skip it.
			if (isDescendantOf(impactScope, visitedScopes, state))
				continue;
			visitedScopes.add(impactScope);
			reachersOfImpactScope = ownerOfScope(impactScope, state,
					allProcesses);
			waitDepedentProcesses = waitDependentProcesses(state,
					reachersOfImpactScope, visitedProcesses);
			for (ProcessState proc : waitDepedentProcesses) {
				int pid = proc.getPid();

				ampleProcesses.add(proc);
				if (!visitedProcesses.contains(pid)) {
					ArrayList<Integer> impScopes = impactScopesOfProcess(proc,
							state);

					visitedProcesses.add(pid);
					for (int iScope : impScopes) {
						if (iScope == state.rootScopeID()) {
							return new LinkedHashSet<>(allProcesses);
						}
						if (!visitedScopes.contains(iScope)) {
							workingScopes.push(iScope);
						}
					}
				}
			}
		}
		return ampleProcesses;
	}

	/**
	 * process P is blocked iff all outgoing statements of its current location
	 * are wait statements
	 * 
	 * @param p
	 *            The process to be checked.
	 * @return
	 */
	private boolean blocked(ProcessState p) {
		for (Statement s : p.getLocation().outgoing()) {
			if (!(s instanceof WaitStatement))
				return false;
		}
		return true;
	}

	/**
	 * Check the correctness of the ample process set only for debugging purpose
	 * 
	 * @param ampleProcesses
	 *            The ample set of processes
	 * @param state
	 *            The state that the ample set is calculated.
	 */
	private void checkCorrectness(ArrayList<ProcessState> ampleProcesses,
			State state) {
		HashSet<Integer> impScopes = new HashSet<>();
		HashSet<Integer> ampleID = new HashSet<>();
		ArrayList<Integer> nonAmpleIDs = new ArrayList<>();

		for (ProcessState p : ampleProcesses) {
			int pScope = p.getDyscopeId();

			ampleID.add(p.getPid());
			for (Statement s : p.getLocation().outgoing()) {
				int impScope = pScope;

				if (s.statementScope() != null) {
					while (!state.getScope(impScope).lexicalScope()
							.equals(s.statementScope())) {
						impScope = state.getParentId(impScope);
					}
					impScopes.add(impScope);
				}
			}
		}
		for (ProcessState p : state.getProcessStates()) {
			int pid = p.getPid();

			if (!ampleID.contains(pid)) {
				nonAmpleIDs.add(pid);
			}
		}
		for (int iscope : impScopes) {
			// DynamicScope dyScope = state.getScope(iscope);
			for (int pid : nonAmpleIDs) {
				if (state.reachableByProcess(iscope, pid)) {
					System.out.println("error ample set found!");
				}
			}
		}
	}

	/**
	 * Attempts to form an ample set from the enabled transitions of the given
	 * process, from the given state. If this is not possible, returns all
	 * transitions.
	 * 
	 * @param state
	 *            The state to work with.
	 * @return The enabled transitions as an instance of TransitionSequence.
	 */
	private TransitionSequence enabledTransitionsScope1(State state) {
		TransitionSequence transitions = transitionFactory
				.newTransitionSequence(state);
		Iterable<? extends ProcessState> processStates = state
				.getProcessStates();
		Map<ProcessState, TransitionSequence> processTransitions = new LinkedHashMap<>();
		int totalTransitions = 0;

		enabledTransitionSets++;
		for (ProcessState p : processStates) {
			TransitionSequence localTransitions = transitionFactory
					.newTransitionSequence(state);
			boolean allLocal = true;
			Location pLocation;
			int pid = p.getPid();
			int locationDyScope = -1;

			// A process with an empty stack has no current location.
			if (p == null || p.hasEmptyStack()) {
				continue;
			}
			pLocation = p.getLocation();
			if (pLocation.enterAtom() || pLocation.enterAtomic()) {
				locationDyScope = locationImpactDyscopeId(state, p, pLocation);
				if (state.numberOfReachers(locationDyScope) > 1) {
					allLocal = false;
				}
			}
			for (Statement s : pLocation.outgoing()) {
				BooleanExpression newPathCondition = newPathCondition(state,
						pid, s);

				if (!newPathCondition.isFalse()) {
					// pLocation is NOT entering any atomic/atom block
					if (locationDyScope == -1) {
						int impactDyScope = statementImpactDyscopeId(state, p,
								s);

						if (state.numberOfReachers(impactDyScope) > 1) {
							allLocal = false;
						}
					}
					localTransitions.addAll(enabledTransitionsOfStatement(
							state, s, newPathCondition, pid, null));
				}
			}
			totalTransitions += localTransitions.size();
			if (allLocal && localTransitions.size() > 0) {
				ampleSets++;
				processTransitions.put(p, localTransitions);
				if (localTransitions.size() == 1) {
					// If the size isn't 1, keep looking for a smaller local
					// set.
					// if(debugging)
					// debugOut.println("Number of transitions at state " +
					// state.getId() + ": " + localTransitions.size());
					if (debugging) {
						debugOut.println("ample processes at state "
								+ state.getCanonicId() + ":");
						debugOut.println(pid);
					}
					return localTransitions;
				}
			} else {
				transitions.addAll(localTransitions);
			}
		}
		if (processTransitions.size() > 0) {
			ProcessState smallestProcess = null;
			int smallestProcessSetSize = totalTransitions + 1;

			for (ProcessState p : processTransitions.keySet()) {
				if (processTransitions.get(p).size() < smallestProcessSetSize) {
					smallestProcess = p;
					smallestProcessSetSize = processTransitions.get(p).size();
				}
			}
			assert smallestProcess != null;
			// System.out.println("Returning " + smallestProcessSetSize +
			// " transitions for 1 process");
			// if(debugging)
			// debugOut.println("Number of transtions at state " + state.getId()
			// + ": " + processTransitions.get(smallestProcess).size());
			if (debugging) {
				debugOut.println("ample processes at state "
						+ state.getCanonicId() + ":");
				debugOut.println(smallestProcess.getPid());
			}
			return processTransitions.get(smallestProcess);
		}
		// System.out.println("Returning " + totalTransitions + " transitions");
		// if(debugging)
		// debugOut.println("Number of transtions at state " + state.getId() +
		// ": " + transitions.size());
		if (debugging) {
			debugOut.println("ample processes at state " + state.getCanonicId()
					+ ":");
			for (ProcessState p : state.getProcessStates()) {
				debugOut.print(p.getPid() + "\t");
			}
			debugOut.println();
		}
		return transitions;
	}

	/**
	 * The new partial order reduction Compute the set of processes that impact
	 * a set of scopes exclusively accessed by the rest of processes.
	 * 
	 * @param state
	 *            The state to work with.
	 * @return The enabled transitions as an instance of TransitionSequence.
	 */
	private TransitionSequence enabledTransitionsScope2(State state) {
		TransitionSequence transitions = transitionFactory
				.newTransitionSequence(state);
		ArrayList<ProcessState> processStates = new ArrayList<>(
				ampleProcesses(state));

		// Compute the ample set (of transitions)
		for (ProcessState p : processStates) {
			transitions.addAll(enabledTransitionsOfProcess(state, p.getPid()));
		}
		if (debugging) {
			checkCorrectness(processStates, state);

			if (processStates.size() > 1) {
				debugOut.println("Number of transtions at state "
						+ state.identifier() + ": " + transitions.size());
				debugOut.println("Number of ample processes: "
						+ processStates.size());
				debugOut.println("Ample process set is : "
						+ processStates.toString());
			}
		}
		return transitions;
	}

	/**
	 * Calculate the set of impact scopes of a process at a certain state. When
	 * the current location of the process is entering an atomic/atom block, the
	 * impact scope should be the total impact scope of the whole atomic/atom
	 * block, i.e., {@link Location#impactScopeOfAtomicOrAtomBlock()}.
	 * 
	 * @param p
	 *            The process to be checked.
	 * @param state
	 *            The current state.
	 * @return The list of dynamic scope ID's that might be affected by p.
	 */
	private ArrayList<Integer> impactScopesOfProcess(ProcessState p, State state) {
		ArrayList<Integer> dyscopes = new ArrayList<>();
		// Obtain the impact scopes of all possible statements of process
		int pScope = p.getDyscopeId();
		Location pLocation = p.getLocation();

		if (pLocation.enterAtom() || pLocation.enterAtomic()) {
			Scope locationImpactScope = pLocation
					.impactScopeOfAtomicOrAtomBlock();
			int impScope;

			if (locationImpactScope != null) {
				impScope = pScope;
				while (!state.getScope(impScope).lexicalScope()
						.equals(locationImpactScope)) {
					impScope = state.getParentId(impScope);
					if (impScope < 0) {
						impScope = pScope;
						break;
					}
				}
				dyscopes.add(impScope);
			}
		} else {
			for (Statement s : p.getLocation().outgoing()) {
				int impScope;

				if (s.hasDerefs()) {
					dyscopes.add(state.rootScopeID());
					return dyscopes;
				}
				impScope = pScope;
				if (s.statementScope() != null) {
					while (!state.getScope(impScope).lexicalScope()
							.equals(s.statementScope())) {
						impScope = state.getParentId(impScope);
					}
					dyscopes.add(impScope);
				}
			}
		}
		return dyscopes;
	}

	/**
	 * Given a dyscope and a set of dyscopes at a state, return true if there
	 * exists an element in the given dyscope set, such that the given dyscope
	 * is a descendant of that element. Otherwise, return false.
	 * 
	 * @param dyscope
	 *            The ID of dyscope to be checked.
	 * @param dyscopeSet
	 *            The set of dyscope ID's that might or might not contain a
	 *            dyscope ID that is the ascendant of the given dyscope.
	 * @param state
	 *            The state to work with, which provides the information of the
	 *            dyscope tree.
	 * @return
	 */
	private boolean isDescendantOf(int dyscope, HashSet<Integer> dyscopeSet,
			State state) {
		int parentScope = dyscope;

		if (dyscopeSet.isEmpty() || dyscopeSet.size() == 0)
			return false;
		while (parentScope != -1) {
			parentScope = state.getParentId(parentScope);
			if (dyscopeSet.contains(parentScope))
				return true;
		}
		return false;
	}

	/**
	 * Return true iff the given wait statement is enabled at the specified
	 * state.
	 * 
	 * @param p
	 *            The process that the wait statement belongs to.
	 * @param state
	 *            The current state.
	 * @param wait
	 *            The wait statement to be checked.
	 * @return True iff the wait statement is enabled at the given state.
	 */
	private boolean isEnabledWait(State state, ProcessState p,
			WaitStatement wait) {
		int joinedPid = evaluator.joinedIDofWait(state, p, wait);
		ProcessState joinedProc = state.getProcessState(joinedPid);

		if (joinedProc == null || joinedProc.hasEmptyStack()) {
			return true;
		}
		return false;
	}

	/**
	 * For a location that enters an atomic/atom block, we need to obtain the
	 * impact dyscope of the whole atomic/atom block.<br>
	 * Precondition:
	 * <code>pLocation.enterAtomic() || pLocation.enterAtom()</code>
	 * 
	 * @param state
	 *            The current state.
	 * @param p
	 *            The process that the location associates with.
	 * @param pLocation
	 *            The location whose impact dyscope is to be calculated.
	 * @return The impact dyscope of the atomic/atom block starting at the given
	 *         location.
	 */
	private int locationImpactDyscopeId(State state, ProcessState p,
			Location pLocation) {
		Scope staticImpactScope = pLocation.impactScopeOfAtomicOrAtomBlock();
		int locationDyScope = p.getDyscopeId();

		if (staticImpactScope != null) {
			while (!state.getScope(locationDyScope).lexicalScope()
					.equals(staticImpactScope)) {
				locationDyScope = state.getParentId(locationDyScope);
				if (locationDyScope < 0) {
					locationDyScope = p.getDyscopeId();
					break;
				}
			}
		}
		return locationDyScope;
	}

	/**
	 * find a good process to start with:
	 * <ol>
	 * <li>the process whose impact scope has the minimal number of reachers;</li>
	 * <li>if all processes are disabled (null, empty-stack, or waiting), then
	 * return the waiting process if there is one or return NULL</li>
	 * </ol>
	 * 
	 * @param state
	 *            The current state.
	 * @param allProcesses
	 *            The list of all active processes (not null or empty-stack) at
	 *            the state.
	 * @return The process selected and the number of reachers of its impact
	 *         scope.
	 */
	private Pair<ProcessState, Integer> minimalReachers(State state,
			ArrayList<ProcessState> allProcesses) {
		int numOfProcs, i, minReachers, minProcIndex;
		ProcessState p, waitProc;
		boolean allDisabled = true;
		HashSet<Integer> vScopes;

		numOfProcs = allProcesses.size();
		i = numOfProcs - 1;
		minReachers = numOfProcs + 1;
		minProcIndex = i;
		waitProc = null;
		vScopes = new HashSet<>();
		do {
			int maxReachers, currentReachers;
			ArrayList<Integer> iScopes;
			boolean newScope;

			p = allProcesses.get(i);
			if (blocked(p)) {
				// if p's current statement is Wait and the joined process
				// has terminated, then p is the ample process set
				if (isEnabledWait(state, p, (WaitStatement) p.getLocation()
						.getOutgoing(0))) {
					return new Pair<>(p, 1);
				}
				waitProc = p;
				i--;
				if (i < 0) {
					if (allDisabled) {
						return new Pair<>(waitProc, 1);
					}
				}
				continue;
			}
			if (p.getLocation().allOutgoingPurelyLocal()) {
				return new Pair<>(p, 1);
			}
			allDisabled = false;
			maxReachers = 0;
			iScopes = impactScopesOfProcess(p, state);
			if (iScopes.isEmpty()) {
				return new Pair<>(p, 1);
			}
			newScope = false;
			for (int impScope : iScopes) {
				if (vScopes.contains(impScope))
					continue;
				newScope = true;
				vScopes.add(impScope);
				// The root scope is reachable from all processes
				if (impScope == state.rootScopeID()) {
					maxReachers = numOfProcs;
					break;
				}
				currentReachers = state.numberOfReachers(impScope);
				// find out the maximal number of reachers that an impact scope
				// of process p can have
				if (currentReachers > maxReachers)
					maxReachers = currentReachers;
			}
			// all impact scopes of p has at most one reacher return p
			// immediately as the ample process set
			if (newScope && maxReachers <= 1) {
				return new Pair<>(p, 1);
			}
			// keep track of the process with least-reacher impact scope
			if (newScope && maxReachers < minReachers) {
				minReachers = maxReachers;
				minProcIndex = i;
			}
			i--;
		} while (i >= 0);
		return new Pair<>(state.getProcessState(minProcIndex), minReachers);
	}

	/**
	 * Given a dyscope at a state, returns the set of processes that owns the
	 * scope. A set of processes owns a dyscope at a certain state, implies that
	 * any process not in the set cannot reach the dyscope at the state.
	 * 
	 * @param dyscope
	 *            The dyscope to be checked.
	 * @param state
	 *            The current state that contains the information of the dyscope
	 *            tree.
	 * @param processes
	 *            The set of processed that might or might not owns the given
	 *            dyscope.
	 * @return the owner (set of processes) of the scope
	 */
	private ArrayList<ProcessState> ownerOfScope(int dyscope, State state,
			ArrayList<ProcessState> processes) {
		ArrayList<ProcessState> reacherProcs = new ArrayList<>();
		int length = processes.size();

		for (int i = 0; i < length; i++) {
			ProcessState p = processes.get(i);

			if (state.reachableByProcess(dyscope, i))
				reacherProcs.add(p);
		}
		return reacherProcs;
	}

	/**
	 * Calculate the impact dyscope ID of a given statement at a certain state.
	 * 
	 * @param state
	 *            The current state.
	 * @param p
	 *            The process that the statement belongs to.
	 * @param s
	 *            The statement to be checked.
	 * @return The impact dyscope ID of the statement at a given state.
	 */
	private int statementImpactDyscopeId(State state, ProcessState p,
			Statement s) {
		int impactDyScope = p.getDyscopeId();

		if (s.statementScope() != null) {
			while (!state.getScope(impactDyScope).lexicalScope()
					.equals(s.statementScope())) {
				impactDyScope = state.getParentId(impactDyScope);
				if (impactDyScope < 0) {
					impactDyScope = p.getDyscopeId();
					break;
				}
			}
		}
		return impactDyScope;
	}

	/**
	 * Compose the list of dependent processes by wait statements. For each
	 * process in the reacher set, if its current statement is a wait statement,
	 * then add the non-terminated process that it waits for to the returned
	 * list.
	 * 
	 * @param state
	 * @param reachersImp
	 * @param visitedProcesses
	 * @return The list of dependent processes by wait statements.
	 */
	private ArrayList<ProcessState> waitDependentProcesses(State state,
			ArrayList<ProcessState> reachersImp,
			HashSet<Integer> visitedProcesses) {
		ArrayList<ProcessState> tmpProcesses = new ArrayList<>();

		for (ProcessState proc : reachersImp) {
			int pid = proc.getPid();

			tmpProcesses.add(proc);
			if (!visitedProcesses.contains(pid)) {
				for (Statement s : proc.getLocation().outgoing()) {
					if (s instanceof WaitStatement) {
						int joinedPid = evaluator.joinedIDofWait(state, proc,
								(WaitStatement) s);

						if (!visitedProcesses.contains(joinedPid)) {
							ProcessState waitedProcess = state
									.getProcessState(joinedPid);

							if (waitedProcess != null
									&& !waitedProcess.hasEmptyStack())
								tmpProcesses.add(waitedProcess);
						}
					}
				}
			}
		}
		return tmpProcesses;
	}

}
