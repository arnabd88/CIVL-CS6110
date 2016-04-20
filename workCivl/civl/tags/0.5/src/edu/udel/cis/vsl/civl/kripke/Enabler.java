package edu.udel.cis.vsl.civl.kripke;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Random;
import java.util.Stack;

import edu.udel.cis.vsl.civl.err.CIVLExecutionException;
import edu.udel.cis.vsl.civl.err.CIVLExecutionException.Certainty;
import edu.udel.cis.vsl.civl.err.CIVLExecutionException.ErrorKind;
import edu.udel.cis.vsl.civl.err.CIVLInternalException;
import edu.udel.cis.vsl.civl.err.CIVLStateException;
import edu.udel.cis.vsl.civl.err.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.AssignStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ChooseStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.statement.WaitStatement;
import edu.udel.cis.vsl.civl.model.common.statement.StatementList;
import edu.udel.cis.vsl.civl.semantics.Evaluation;
import edu.udel.cis.vsl.civl.semantics.Evaluator;
import edu.udel.cis.vsl.civl.semantics.Executor;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.transition.SimpleTransition;
import edu.udel.cis.vsl.civl.transition.Transition;
import edu.udel.cis.vsl.civl.transition.TransitionFactory;
import edu.udel.cis.vsl.civl.transition.TransitionSequence;
import edu.udel.cis.vsl.gmc.EnablerIF;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;

/**
 * Enabler implements {@link EnablerIF} for CIVL models. Its basic functionality
 * is to obtain the set of enabled transitions of a certain state. Currently,
 * there are two partial order reduction algorithms in Enabler, namely standard
 * POR ({@link #enabledTransitionsPOR(State)}) and scoped POR (
 * {@link #enabledTransitionsPORscoped(State)}). By default, the standard POR is
 * used.
 * 
 * @author Manchun Zheng (zmanchun)
 * @author Timothy K. Zirkel (zirkel)
 */
public class Enabler implements
		EnablerIF<State, Transition, TransitionSequence> {

	/***************************** Instance Fields ***************************/

	/**
	 * The number of ample sets, initialized as 0.
	 */
	private long ampleSets = 0;

	/**
	 * Turn on/off debugging option to print more information.
	 */
	private boolean debugging = false;

	/**
	 * The output stream for printing debugging information.
	 */
	private PrintStream debugOut = System.out;

	/**
	 * The unique evaluator used by the system.
	 */
	private Evaluator evaluator;

	/**
	 * The unique executor used by the system.
	 */
	private Executor executor;

	/**
	 * The number of enabled
	 */
	private long enabledTransitionSets = 0;

	/**
	 * The unique random number generator used by the system.
	 */
	private Random generator = null;

	/**
	 * The unique model factory used by the system.
	 */
	private ModelFactory modelFactory;

	private boolean randomMode = false;

	/**
	 * true iff want to use the new scope POR algorithm
	 */
	public boolean scpPor = false;

	/**
	 * The unique transition factory used by the system.
	 */
	private TransitionFactory transitionFactory;

	/**
	 * The unique symbolic universe used by the system.
	 */
	private SymbolicUniverse universe;

	/******************************* Constructors ****************************/

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
	 */
	public Enabler(TransitionFactory transitionFactory, Evaluator evaluator,
			Executor executor, boolean sPor) {
		this.transitionFactory = transitionFactory;
		this.evaluator = evaluator;
		this.executor = executor;
		this.modelFactory = evaluator.modelFactory();
		this.universe = modelFactory.universe();
		this.scpPor = sPor;
		if (this.scpPor)
			this.debugOut.println("scoped POR is enabled.");
	}

	/**
	 * 
	 * @param transitionFactory
	 *            The transition factory to be used in this enabler.
	 * @param evaluator
	 *            The evaluator to be used to calculate and evaluate new path
	 *            condition
	 * @param executor
	 *            The executor to be used
	 * @param randomMode
	 *            True if want to run in random mode, in which case exactly one
	 *            transition will be chosen randomly to return
	 * @param generator
	 *            The unique random number generator to be used for random mode
	 *            execution.
	 * @param sPor
	 *            True iff want to use scoped POR instead of default POR.
	 */
	public Enabler(TransitionFactory transitionFactory, Evaluator evaluator,
			Executor executor, boolean randomMode, Random generator,
			boolean sPor) {
		this(transitionFactory, evaluator, executor, sPor);
		this.randomMode = randomMode;
		this.generator = generator;
	}

	/************************** Methods from EnablerIF ***********************/

	@Override
	public boolean debugging() {
		return debugging;
	}

	@Override
	public TransitionSequence enabledTransitions(State state) {
		TransitionSequence transitions;
		ArrayList<Integer> resumableProcesses;
		ProcessState p;
		AssignStatement assignStatement;
		Location pLocation;

		if (state.getPathCondition().isFalse())
			// return empty set of transitions:
			return new TransitionSequence(state);
		p = executor.stateFactory().processInAtomic(state);
		if (p != null) {
			// execute a transition in an atomic block of a certain process
			// without interleaving with other processes
			TransitionSequence localTransitions = transitionFactory
					.newTransitionSequence(state);
			int pid = p.getPid();

			localTransitions.addAll(getTransitions(state, pid, null));
			if (localTransitions.isEmpty()) {
				// release atomic lock if the current location of the process
				// that holds the lock is blocked
				state = executor.stateFactory().releaseAtomicLock(state);
			} else
				return localTransitions;
		}
		// TODO optimize the number of valid/prover calls
		resumableProcesses = executor.resumableAtomicProcesses(state);
		if (resumableProcesses.size() == 1) {
			int pid = resumableProcesses.get(0);

			pLocation = state.getProcessState(pid).getLocation();
			assignStatement = modelFactory.assignAtomicLockVariable(pid,
					pLocation);
			// only one process in atomic blocks could be resumed, so let
			// the process hold the atomic lock
			transitions = transitionFactory.newTransitionSequence(state);
			transitions.addAll(getTransitions(state, pid, assignStatement));
			if (transitions.isEmpty()) {
				throw new CIVLInternalException("unreachable", p.getLocation()
						.getSource());
			}
			return transitions;
		} else if (resumableProcesses.size() > 1) {
			// There are more than one processes trying to hold the atomic lock
			transitions = transitionFactory.newTransitionSequence(state);
			for (Integer pid : resumableProcesses) {
				pLocation = state.getProcessState(pid).getLocation();
				assignStatement = modelFactory.assignAtomicLockVariable(pid,
						pLocation);
				transitions.addAll(getTransitions(state, pid, assignStatement));
			}
			return transitions;
		}
		if (!this.scpPor) {
			if (debugging && enabledTransitionSets % 1000 == 0) {
				System.out.println("Ample transition sets: " + ampleSets + "/"
						+ enabledTransitionSets);
			}
			transitions = enabledTransitionsPOR(state);
			if (debugging) {
				if (transitions.size() > 1) {
					debugOut.println("Number of transitions at state "
							+ state.identifier() + "is " + transitions.size());
					state.print(debugOut);
				}
			}
		} else
			transitions = enabledTransitionsPORsoped(state);
		if (randomMode && transitions.size() > 0) {
			TransitionSequence singletonSequence = new TransitionSequence(state);
			singletonSequence.add(transitions.get(generator.nextInt(transitions
					.size())));
			return singletonSequence;
		}
		return transitions;
	}

	@Override
	public PrintStream getDebugOut() {
		return debugOut;
	}

	@Override
	public boolean hasMultiple(TransitionSequence sequence) {
		return sequence.numRemoved() + sequence.size() > 1;
	}

	@Override
	public boolean hasNext(TransitionSequence transitionSequence) {
		return !transitionSequence.isEmpty();
	}

	@Override
	public Transition next(TransitionSequence transitionSequence) {
		return transitionSequence.remove();
	}

	@Override
	public int numRemoved(TransitionSequence sequence) {
		return sequence.numRemoved();
	}

	@Override
	public Transition peek(TransitionSequence transitionSequence) {
		return transitionSequence.peek();
	}

	@Override
	public void print(PrintStream out, TransitionSequence transitionSequence) {
	}

	@Override
	public void printFirstTransition(PrintStream arg0, TransitionSequence arg1) {
	}

	@Override
	public void printRemaining(PrintStream arg0, TransitionSequence arg1) {
	}

	@Override
	public void setDebugOut(PrintStream debugOut) {
		this.debugOut = debugOut;
	}

	@Override
	public void setDebugging(boolean debugging) {
		this.debugging = debugging;
	}

	@Override
	public State source(TransitionSequence transitionSequence) {
		return transitionSequence.state();
	}

	/***************************** Private Methods ***************************/

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
		int numOfProcs, i, minReachers, minProcIndex;
		ProcessState p, waitProc;
		boolean allDisabled = true;
		HashSet<Integer> vScopes;
		ArrayList<Integer> iScopesP;

		for (ProcessState tmp : state.getProcessStates()) {
			if (tmp == null || tmp.hasEmptyStack())
				continue;
			allProcesses.add(tmp);
		}
		if (allProcesses.isEmpty())
			return ampleProcesses;
		numOfProcs = allProcesses.size();
		i = numOfProcs - 1;
		minReachers = numOfProcs + 1;
		minProcIndex = i;
		waitProc = null;
		// find a good process to start 1. if there exist a process whose impact
		// scope is owned by itself, then return the process as the ample
		// process set immediately; 2. skip null or empty-stack process 3. if
		// all process are disabled (null, empty-stack, or waiting), then ample
		// process will contain a waiting process if there is one or it will be
		// empty
		vScopes = new HashSet<>();
		do {
			int maxReachers, currentReachers;
			ArrayList<Integer> iScopes;
			boolean newScope;

			p = allProcesses.get(i);
			if (blocked(p)) {
				// if p's current statement is Wait and the joined process
				// has terminated, then p is the ample process set
				if (isEnabledWait(p, state)) {
					ampleProcesses.add(p);
					return ampleProcesses;
				}
				waitProc = p;
				i--;
				if (i < 0) {
					if (allDisabled) {
						if (waitProc != null)
							ampleProcesses.add(waitProc);
						return ampleProcesses;
					}
				}
				continue;
			}
			if (p.getLocation().allOutgoingPurelyLocal()) {
				ampleProcesses.add(p);
				return ampleProcesses;
			}
			allDisabled = false;
			maxReachers = 0;
			iScopes = impactScopesOfProcess(p, state);
			if (iScopes.isEmpty()) {
				ampleProcesses.add(p);
				return ampleProcesses;
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
				ampleProcesses.add(p);
				return ampleProcesses;
			}
			// keep track of the process with least-reacher impact scope
			if (newScope && maxReachers < minReachers) {
				minReachers = maxReachers;
				minProcIndex = i;
			}
			i--;
		} while (i >= 0);
		// If the minimal number of reachers equals to the number of processes
		// return all processes as the ample set immediately
		if (minReachers == numOfProcs) {
			ampleProcesses.addAll(allProcesses);
			return ampleProcesses;
		}
		// Start from p, whose impact factor has the least number of reachers
		p = allProcesses.get(minProcIndex);
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
			int impScope = workingScopes.pop();
			ArrayList<ProcessState> reachersImp;
			ArrayList<ProcessState> tmpProcesses;

			// If imScope is a descendant of some dyscope in visitedScopes, all
			// its owner processes are all in ampleProcesses already. Thus skip
			// it.
			if (isDescendantOf(impScope, visitedScopes, state))
				continue;
			visitedScopes.add(impScope);
			// reachersImp is the set of procceses that can reach imScope
			reachersImp = ownerOfScope(impScope, state, allProcesses);
			tmpProcesses = new ArrayList<>();
			// For each process in reacher set, if its current statement is
			// wait, add the process that it waits for to a new "reacher set"
			// (tmpProcesses).
			for (ProcessState proc : reachersImp) {
				int pid = proc.getPid();

				tmpProcesses.add(proc);
				if (!visitedProcesses.contains(pid)) {
					for (Statement s : proc.getLocation().outgoing()) {
						if (s instanceof WaitStatement) {
							try {
								WaitStatement wait = (WaitStatement) s;
								Evaluation eval = evaluator.evaluate(state,
										pid, wait.process());
								SymbolicExpression procVal = eval.value;
								int joinedPid = modelFactory.getProcessId(wait
										.process().getSource(), procVal);

								if (!visitedProcesses.contains(joinedPid)) {
									ProcessState waitedProcess = state
											.getProcessState(joinedPid);
									if (proc != null && !proc.hasEmptyStack())
										tmpProcesses.add(waitedProcess);
								}
							} catch (UnsatisfiablePathConditionException ex) {
							}
						}
					}
				}

			}
			// tmpProcesses contains the reacher set of impScope and all
			// processes being waited for by some process in impScope
			for (ProcessState proc : tmpProcesses) {
				int pid = proc.getPid();

				ampleProcesses.add(proc);
				if (!visitedProcesses.contains(pid)) {
					ArrayList<Integer> impScopes = impactScopesOfProcess(proc,
							state);

					visitedProcesses.add(pid);
					for (int iScope : impScopes) {
						if (iScope == state.rootScopeID()) {
							ampleProcesses = new LinkedHashSet<>(allProcesses);
							return ampleProcesses;
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
	 * Get the enabled transitions of a statement at a certain state. An
	 * assignment to the atomic lock variable might be forced to the returned
	 * transitions, when the process is going to re-obtain the atomic lock
	 * variable.
	 * 
	 * @param state
	 *            The state to work with.
	 * @param s
	 *            The statement to be used to generate transitions.
	 * @param pathCondition
	 *            The current path condition.
	 * @param pid
	 *            The process id that the statement belongs to.
	 * @param assignAtomicLock
	 *            The assignment statement for the atomic lock variable, should
	 *            be null except that the process is going to re-obtain the
	 *            atomic lock variable.
	 * @return The set of enabled transitions.
	 */
	private ArrayList<SimpleTransition> enabledTransitionsOfStatement(
			State state, Statement s, BooleanExpression pathCondition, int pid,
			Statement assignAtomicLock) {
		ArrayList<SimpleTransition> localTransitions = new ArrayList<>();
		Statement transitionStatement;

		try {
			if (s instanceof ChooseStatement) {
				Evaluation eval = evaluator.evaluate(
						state.setPathCondition(pathCondition), pid,
						((ChooseStatement) s).rhs());
				IntegerNumber upperNumber = (IntegerNumber) universe.reasoner(
						eval.state.getPathCondition()).extractNumber(
						(NumericExpression) eval.value);
				int upper;

				if (upperNumber == null)
					throw new CIVLStateException(ErrorKind.INTERNAL,
							Certainty.NONE,
							"Argument to $choose_int not concrete: "
									+ eval.value, eval.state, s.getSource());
				upper = upperNumber.intValue();
				if (assignAtomicLock != null) {
					StatementList statementList = new StatementList(
							assignAtomicLock);

					statementList.add(s);
					transitionStatement = statementList;
				} else {
					transitionStatement = s;
				}
				for (int i = 0; i < upper; i++) {
					localTransitions.add(transitionFactory.newChooseTransition(
							eval.state.getPathCondition(), pid,
							transitionStatement, universe.integer(i)));
				}
			} else if (s instanceof WaitStatement) {
				Evaluation eval = evaluator.evaluate(
						state.setPathCondition(pathCondition), pid,
						((WaitStatement) s).process());
				int pidValue = modelFactory.getProcessId(((WaitStatement) s)
						.process().getSource(), eval.value);

				if (pidValue < 0) {
					CIVLExecutionException e = new CIVLStateException(
							ErrorKind.INVALID_PID,
							Certainty.PROVEABLE,
							"Unable to call $wait on a process that has already been the target of a $wait.",
							state, s.getSource());

					evaluator.reportError(e);
					// TODO: recover: add a no-op transition
					throw e;
				}
				if (state.getProcessState(pidValue).hasEmptyStack()) {
					if (assignAtomicLock != null) {
						StatementList statementList = new StatementList(
								assignAtomicLock);

						statementList.add(s);
						transitionStatement = statementList;
					} else {
						transitionStatement = s;
					}
					localTransitions.add(transitionFactory.newSimpleTransition(
							pathCondition, pid, transitionStatement));
				}
			} else {
				if (assignAtomicLock != null) {
					StatementList statementList = new StatementList(
							assignAtomicLock);

					statementList.add(s);
					transitionStatement = statementList;
				} else {
					transitionStatement = s;
				}
				localTransitions.add(transitionFactory.newSimpleTransition(
						pathCondition, pid, transitionStatement));
			}
		} catch (UnsatisfiablePathConditionException e) {
			// nothing to do: don't add this transition
		}
		return localTransitions;
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
	private TransitionSequence enabledTransitionsPOR(State state) {
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
				// for a location that enters an atomic/atom block, we need to
				// obtain the impact scope of the whole atomic/atom block
				Scope staticImpactScope = pLocation
						.impactScopeOfAtomicOrAtomBlock();
				locationDyScope = p.getDyscopeId();

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
				if (state.numberOfReachers(locationDyScope) > 1) {
					allLocal = false;
				}
			}
			for (Statement s : pLocation.outgoing()) {
				BooleanExpression newPathCondition = executor.newPathCondition(
						state, pid, s);

				if (locationDyScope == -1) { // this implies that pLocation is
												// not entering any atomic/atom
												// block
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
					if (state.numberOfReachers(impactDyScope) > 1) {
						allLocal = false;
					}
				}
				if (!newPathCondition.isFalse()) {
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
			return processTransitions.get(smallestProcess);
		}
		// System.out.println("Returning " + totalTransitions + " transitions");
		// if(debugging)
		// debugOut.println("Number of transtions at state " + state.getId() +
		// ": " + transitions.size());
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
	private TransitionSequence enabledTransitionsPORsoped(State state) {
		TransitionSequence transitions = transitionFactory
				.newTransitionSequence(state);
		ArrayList<ProcessState> processStates = new ArrayList<>(
				ampleProcesses(state));

		// Compute the ample set (of transitions)
		for (ProcessState p : processStates) {
			TransitionSequence localTransitions = transitionFactory
					.newTransitionSequence(state);
			int pid = p.getPid();

			// No need to check if p is null/empty stack, since
			// it is already checked in ampleProcesses()
			// A process with an empty stack has no current location.
			for (Statement s : p.getLocation().outgoing()) {
				BooleanExpression newPathCondition = executor.newPathCondition(
						state, pid, s);

				// No need to calculate impact scope, since everything in
				// processStates is already ample set processes generate
				// transitions for each statement of each process
				if (!newPathCondition.isFalse()) {
					localTransitions.addAll(enabledTransitionsOfStatement(
							state, s, newPathCondition, pid, null));
				}
			}
			// add all possible transitions of a process to the ample
			// set(transitions)
			transitions.addAll(localTransitions);
		}

		if (debugging) {
			checkCorrectness(processStates, state);
			// debugOut.println("Number of all processes: " +
			// state.processes().length);

			if (processStates.size() > 1) {
				debugOut.println("Number of transtions at state "
						+ state.identifier() + ": " + transitions.size());
				debugOut.println("Number of ample processes: "
						+ processStates.size());
				debugOut.println("Ample process set is : "
						+ processStates.toString());
				// state.print(debugOut);
			}
		}

		return transitions;
	}

	/**
	 * Get the enabled transitions of a certain process at a given state.
	 * 
	 * @param state
	 *            The state to work with.
	 * @param pid
	 *            The process id to work with.
	 * @param assignAtomicLock
	 *            The assignment statement for the atomic lock variable, should
	 *            be null except that the process is going to re-obtain the
	 *            atomic lock variable.
	 * @return the list of enabled transitions of the given process at the
	 *         specified state
	 */
	private ArrayList<Transition> getTransitions(State state, int pid,
			Statement assignAtomicLock) {
		ProcessState p = state.getProcessState(pid);
		Location pLocation = p.getLocation();
		ArrayList<Transition> transitions = new ArrayList<>();

		if (pLocation == null)
			return transitions;
		for (Statement s : pLocation.outgoing()) {
			BooleanExpression newPathCondition = executor.newPathCondition(
					state, pid, s);

			if (!newPathCondition.isFalse()) {
				transitions.addAll(enabledTransitionsOfStatement(state, s,
						newPathCondition, pid, assignAtomicLock));
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
	 * Return true iff p's current statement is Wait and is enabled at a certain
	 * state.
	 * 
	 * @param p
	 *            The process to be checked.
	 * @param state
	 *            The current state
	 * @return True iff p's current statement is Wait and is enabled at a
	 *         certain state.
	 */
	private boolean isEnabledWait(ProcessState p, State state) {
		if (p.getLocation().getNumOutgoing() == 1) {
			int pid = p.getPid();
			Statement s = p.getLocation().getOutgoing(0);

			if (s instanceof WaitStatement) {
				try {
					WaitStatement wait = (WaitStatement) s;
					Evaluation eval = evaluator.evaluate(state, pid,
							wait.process());
					SymbolicExpression procVal = eval.value;
					int joinedPid = modelFactory.getProcessId(wait.process()
							.getSource(), procVal);
					ProcessState joinedProc = state.getProcessState(joinedPid);

					if (joinedProc == null || joinedProc.hasEmptyStack()) {
						return true;
					}
				} catch (UnsatisfiablePathConditionException ex) {
				}
			}
		}
		return false;
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

}
