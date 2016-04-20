package edu.udel.cis.vsl.civl.kripke.common;

import java.io.PrintStream;
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.kripke.IF.LibraryEnabler;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.SystemFunction;
import edu.udel.cis.vsl.civl.model.IF.expression.MemoryUnitExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryLoaderException;
import edu.udel.cis.vsl.civl.semantics.IF.MemoryUnitEvaluator;
import edu.udel.cis.vsl.civl.state.IF.MemoryUnit;
import edu.udel.cis.vsl.civl.state.IF.MemoryUnitFactory;
import edu.udel.cis.vsl.civl.state.IF.MemoryUnitSet;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.StackEntry;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.sarl.IF.SARLException;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicCollection;

/**
 * This class is responsible for computing the ample processes set at a given
 * state. It is a helper of Enabler.
 * 
 * Basic ingredients. Need to know, in a state s:
 * 
 * For each process p, what is the set of memory units that p can reach from its
 * call stack?
 * 
 * For each process p, given an enabled statement in p, what are the memory
 * units that could read/written to by that statement.
 * 
 * Questions:
 * 
 * Representation of set of memory units:
 * 
 * How much of this can be computed statically?
 * 
 * Can this information be stored in state and updated incrementally with each
 * transition?
 * 
 * <pre>
 * Fix a process <code>p</code>, computes the set of processes that have to be
 * in the ample set by examining the relation of the impact/reachable memory
 * units of the processes.
 * 
 * Impact memory unit set: all memory units to be accessed (read or written) by a
 * process <code>p</code> at a certain state <code>s</code>. Usually this
 * includes the memory units through the variables appearing in the statements 
 * (including its guard) that originates from <code>p</code>'s location at 
 * <code>s</code>.
 * 
 * Reachable memory unit set: all memory units reachable by a process
 * <code>p</code> at a certain state <code>s</code>. This includes all memory units 
 * reachable through all the variables in the dyscopes visible to <code>p</code>.
 * 
 * Reachable memory unit access annotation: for each element in the reachable memory
 * unit set, annotates the information if the process is possible to write it now or
 * in the future. Immediately, any variable appearing as the left-hand-side of
 * Note, all variables that ever appear as the operand of the address-of (&)
 * operator are to be considered as possibly written by any process. Given a memory 
 * unit <code>m</code> and a process <code>p</code>, <code>w(m, p, s)</code> is true 
 * iff <code>p</code> is possible to write to <code>m</code> from <code>s</code>.
 * 
 * Note: the heap is excluded when computing the impact/reachable memory units; 
 * memory of handle types (such as gcomm/comm, gbarrier/barrier) are ignored.
 * 
 * Ample set algorithm: 
 * 0. Let <code>amp(p)</code> be the ample set of <code>p</code>. Initially, 
 *    <code>amp(p) = { p }</code>. Let <code>work = { p }</code> be the 
 *    set of working processes.
 * 1. Let <code>sys(p, s)</code> be the set of system function calls of <code>p</code>
 * 	  origins at <code>s</code>. Let <code>imp(p, s)</code> be the impact memory set 
 *    of <code>p</code> at state <code>s</code>; remove <code>p</code> from work.
 * 2. For every system call <code>c</code> of <code>sys(p, s)</code>, obtain the ample
 *    set <code>amp(c, p, s)</code> from the corresponding library. Then, for every 
 *    <code>q</code> in <code>amp(c, p, s)</code>, perform 2.1:
 *    2.1. add <code>q</code> to <code>amp(p)</code>, and add <code>q</code> to <code>work</code> 
 *         if <code>q</code> hasn't been added to <code>work</code> before.
 * 3. For every process <code>q</code> active at state <code>s</code>, 
 *    let <code>rea(q, s)</code> be the map of reachable memory units and 
 *    the access annotation (read only or possible write) of process <code>q</code> 
 *    at state <code>s</code>, then do the following:
 *    - for every memory unit <code>m</code> in <code>imp(p, s)</code>, 
 *      find out all memory units <code>m'</code> belonging to <code>rea(q, s)</code> 
 *      that intersects with <code>m</code>;
 *    - if there exists <code>m'</code>, such that <code>w(m, p, s)</code> or
 *      <code>w(m', q, s)</code>, then perform step 2.1 for <code>q</code>.
 * 4. Repeat steps 1-3 until <code>work</code> is empty.
 * </pre>
 * 
 * The ample set worker always return the minimal ample set, i.e., the set with
 * the smallest number of processes. To achieve this, it greedily computes the
 * ample set of all active processes. Sometimes, it doesn't have to iterates
 * over all processes if it finds an ample set of size one.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class AmpleSetWorker {

	/* ********************************* Types ***************************** */

	/**
	 * The status of the computation of memory units: used in
	 * {@link#impactMemoryUnits}, when the result is INCOMPLETE it means that
	 * the approximation of the impact memory units not done and thus it could
	 * be anything (thus the ample set will be all processes); in contrast,
	 * NORMAL means that the computation is done and can be used to calculate
	 * the ample set.
	 * 
	 * @author Manchun Zheng (zmanchun)
	 * 
	 */
	// private enum MemoryUnitsStatus {
	// NORMAL, INCOMPLETE
	// };

	/* *************************** Instance Fields ************************* */

	Map<Integer, Map<Statement, SymbolicExpression>> newGuardMap;

	BitSet waitMap[];

	BitSet nonEmptyProcesses = new BitSet();
	// Set<Integer> allProcesses = new LinkedHashSet<>();

	/**
	 * The map of active processes (i.e., non-null processes with non-empty
	 * stack that have at least one enabled statement)
	 */
	BitSet activeProcesses = new BitSet();

	/**
	 * The unique enabler used in the system. Used here for evaluating the guard
	 * of statements.
	 */
	private CommonEnabler enabler;

	// /**
	// * The unique evaluator of the system. Used to evaluate expressions and
	// * variables for calculating impact or reachable memory units and so on.
	// */
	// private Evaluator evaluator;

	private MemoryUnitEvaluator memUnitEvaluator;

	/**
	 * Turn on/off the printing of debugging information for the ample set
	 * algorithm.
	 */
	private boolean debugging = true;

	/**
	 * The output stream used for debugging.
	 */
	private PrintStream debugOut = System.out;

	private ModelFactory modelFactory;

	/**
	 * map of process ID's and their impact memory units (NULL impact memory
	 * units means that the computation is incomplete and all active processes
	 * should be included in the ample set)
	 */
	// Map<Integer, Set<SymbolicExpression>> impactMemUnitsMap = new
	// HashMap<>();
	MemoryUnitSet[] impactMemUnits;

	int procBound = -1;

	/**
	 * map of process ID's and their reachable memory units with information
	 * that whether the memory unit is to be written.
	 */
	// Map<Integer, Map<SymbolicExpression, Boolean>> reachableMemUnitsMap = new
	// HashMap<>();

	// /**
	// * map of communicators and the sets of process ID's with different ranks
	// of
	// * the communicator
	// */
	// Map<SymbolicExpression, Map<Integer, Set<Integer>>> processesInCommMap =
	// new HashMap<>();
	//
	// /**
	// * map of process ID's and its rank id in each communicator.
	// */
	// Map<Integer, Map<SymbolicExpression, Integer>> processRankMap = new
	// HashMap<>();

	// /**
	// * map of process ID's and the set of enabled system call statements.
	// */
	Map<Integer, Set<CallOrSpawnStatement>> enabledSystemCallMap = new HashMap<>();

	/**
	 * The current state at which the ample set is to be computed.
	 */
	private State state;

	SymbolicUtility symbolicUtil;

	SymbolicUniverse universe;

	MemoryUnitFactory memUnitFactory;

	MemoryUnitSet[] reachableNonPtrReadonly;

	MemoryUnitSet[] reachableNonPtrWritable;

	MemoryUnitSet[] reachablePtrReadonly;

	MemoryUnitSet[] reachablePtrWritable;

	/* ***************************** Constructors ************************** */

	/**
	 * Creates a new instance of ample set worker for a given state.
	 * 
	 * @param state
	 *            The state that this ample set is going to work for.
	 * @param enabler
	 *            The enabler used in the system.
	 * @param evaluator
	 *            The evaluator used in the system.
	 * @param symbolicAnalyzer
	 *            The symbolic analyzer used in the system.
	 * @param debug
	 *            The option to turn on/off the printing of debugging
	 *            information.
	 * @param debugOut
	 *            The print stream for debugging information.
	 */
	AmpleSetWorker(State state, CommonEnabler enabler, Evaluator evaluator,
			MemoryUnitFactory muFactory, int procBound, boolean debug,
			PrintStream debugOut) {
		this.memUnitEvaluator = evaluator.memoryUnitEvaluator();
		this.modelFactory = evaluator.modelFactory();
		this.state = state;
		this.enabler = enabler;
		// this.evaluator = evaluator;
		this.debugging = debug;
		this.debugOut = debugOut;
		this.symbolicUtil = evaluator.symbolicUtility();
		this.universe = evaluator.universe();
		impactMemUnits = new MemoryUnitSet[state.numProcs()];
		this.memUnitFactory = muFactory;
		this.procBound = procBound;
	}

	/* *********************** Package-private Methods ********************* */

	/**
	 * Obtains the set of ample processes for the current state.
	 * 
	 * @return
	 */
	Set<ProcessState> ampleProcesses() {
		BitSet ampleProcessIDs;
		Set<ProcessState> ampleProcesses = new LinkedHashSet<>();

		computeActiveProcesses();
		if (activeProcesses.cardinality() <= 1)
			// return immediately if at most one process is activated.
			ampleProcessIDs = this.activeProcesses;
		else
			ampleProcessIDs = ampleProcessesWork();
		for (int pid = 0; pid < ampleProcessIDs.length(); pid++) {
			pid = ampleProcessIDs.nextSetBit(pid);
			ampleProcesses.add(state.getProcessState(pid));
		}
		return ampleProcesses;
	}

	/* *************************** Private Methods ************************* */

	/**
	 * Computes the ample set when there are more than one active processes.
	 * 
	 * @return The set of process ID's to be contained in the ample set.
	 */
	private BitSet ampleProcessesWork() {
		BitSet result = new BitSet();
		int minimalAmpleSetSize = activeProcesses.cardinality() + 1;

		preprocessing();
		for (int pid = 0; pid < activeProcesses.length(); pid++) {
			BitSet ampleSet;
			int currentSize;

			pid = activeProcesses.nextSetBit(pid);
			ampleSet = ampleSetOfProcess(pid, minimalAmpleSetSize);
			currentSize = ampleSet.cardinality();
			if (currentSize == 1)
				return ampleSet;
			if (currentSize < minimalAmpleSetSize) {
				result = ampleSet;
				minimalAmpleSetSize = currentSize;
			}
		}
		return result;
	}

	/**
	 * Computes the ample set by fixing a certain process and looking at system
	 * calls and impact/reachable memory units.
	 * 
	 * @param startPid
	 *            The id of the process to start with.
	 * @return The set of process ID's to be contained in the ample set.
	 */
	private BitSet ampleSetOfProcess(int startPid, int minAmpleSize) {
		BitSet ampleProcessIDs = new BitSet();
		Stack<Integer> workingProcessIDs = new Stack<>();
		int myAmpleSetActiveSize = 1;

		workingProcessIDs.add(startPid);
		ampleProcessIDs.set(startPid);
		while (!workingProcessIDs.isEmpty()) {
			int pid = workingProcessIDs.pop();
			ProcessState procState = state.getProcessState(pid);
			MemoryUnitSet impactMUSet = impactMemUnits[pid];
			// Map<SymbolicExpression, Boolean> reachableMemUnitsMapOfThis =
			// reachableMemUnitsMap
			// .get(pid);
			Set<CallOrSpawnStatement> systemCalls = this.enabledSystemCallMap
					.get(pid);

			if (impactMUSet == null) {
				// The current process is entering an atomic/atom block
				// whose impact memory units can't be computed
				// completely
				ampleProcessIDs = activeProcesses;
				return ampleProcessIDs;
			}
			if (procBound > 0) {
				for (Statement statement : procState.getLocation().outgoing()) {
					if (statement instanceof CallOrSpawnStatement) {
						CallOrSpawnStatement callOrSpawn = (CallOrSpawnStatement) statement;

						if (callOrSpawn.isSpawn()) {
							for (int otherPid = 0; otherPid < nonEmptyProcesses
									.length(); otherPid++) {
								otherPid = nonEmptyProcesses
										.nextSetBit(otherPid);
								if (otherPid == pid
										|| ampleProcessIDs.get(otherPid))
									continue;
								if (state.getProcessState(otherPid)
										.getLocation().hasSpawn()) {
									if (this.activeProcesses.get(otherPid)) {
										myAmpleSetActiveSize++;
										workingProcessIDs.add(otherPid);
										ampleProcessIDs.set(otherPid);
									} else if (!this
											.isWaitingFor(otherPid, pid)) {
										workingProcessIDs.add(otherPid);
										ampleProcessIDs.set(otherPid);
									}
									if (myAmpleSetActiveSize >= minAmpleSize
											|| myAmpleSetActiveSize == activeProcesses
													.cardinality()) {
										return this.intersects(ampleProcessIDs,
												activeProcesses);
									}
								}
							}
						}
					}
				}

			}
			if (systemCalls != null && !systemCalls.isEmpty()) {
				for (CallOrSpawnStatement call : systemCalls) {
					SystemFunction systemFunction = (SystemFunction) call
							.function();
					BitSet ampleSubSet = null;

					try {
						LibraryEnabler lib = enabler.libraryEnabler(
								call.getSource(), systemFunction.getLibrary());

						ampleSubSet = lib.ampleSet(state, pid, call,
								this.reachablePtrWritable,
								this.reachablePtrReadonly,
								this.reachableNonPtrWritable,
								this.reachableNonPtrReadonly);
					} catch (LibraryLoaderException e) {
						throw new CIVLInternalException(
								"This is unreachable because the earlier execution "
										+ "has already checked that the library enabler "
										+ "gets loaded successfully otherwise an error should have been reported there",
								call.getSource());
					} catch (UnsatisfiablePathConditionException e) {
						// error occur in the library enabler, returns all
						// processes as the ample set.
						ampleProcessIDs = activeProcesses;
						return ampleProcessIDs;
					}
					if (ampleSubSet != null && !ampleSubSet.isEmpty()) {
						for (int amplePid = 0; amplePid < ampleSubSet.length(); amplePid++) {
							amplePid = ampleSubSet.nextSetBit(amplePid);
							if (amplePid != pid
									&& !ampleProcessIDs.get(amplePid)
									&& !workingProcessIDs.contains(amplePid)) {
								if (this.activeProcesses.get(amplePid)) {
									myAmpleSetActiveSize++;
									workingProcessIDs.add(amplePid);
									ampleProcessIDs.set(amplePid);
								} else if (!this.isWaitingFor(amplePid, pid)) {
									workingProcessIDs.add(amplePid);
									ampleProcessIDs.set(amplePid);
								}
								// early return
								if (myAmpleSetActiveSize >= minAmpleSize
										|| myAmpleSetActiveSize == activeProcesses
												.cardinality()) {
									// ampleProcessIDs = intersects(
									// ampleProcessIDs, activeProcesses);
									// ampleProcessIDs.retainAll(activeProcesses);
									return intersects(ampleProcessIDs,
											activeProcesses);
								}
							}
						}
					}
				}
			}
			for (int otherPid = 0; otherPid < nonEmptyProcesses.length(); otherPid++) {
				otherPid = nonEmptyProcesses.nextSetBit(otherPid);
				if (otherPid == pid || ampleProcessIDs.get(otherPid))
					continue;
				for (MemoryUnit mu : impactMUSet.memoryUnits()) {
					if (this.hasAccessConflict(pid, otherPid, mu)) {
						if (this.activeProcesses.get(otherPid)) {
							myAmpleSetActiveSize++;
							workingProcessIDs.add(otherPid);
							ampleProcessIDs.set(otherPid);
						} else if (!this.isWaitingFor(otherPid, pid)) {
							workingProcessIDs.add(otherPid);
							ampleProcessIDs.set(otherPid);
						}
						break;
					}
				}
				// early return
				if (myAmpleSetActiveSize >= minAmpleSize
						|| myAmpleSetActiveSize == activeProcesses
								.cardinality()) {
					return this.intersects(ampleProcessIDs, activeProcesses);
				}
			}
		}
		return this.intersects(ampleProcessIDs, activeProcesses);
	}

	// is pid1 waiting for pid2?
	private boolean isWaitingFor(int pid1, int pid2) {
		if (this.waitMap[pid1] != null)
			return waitMap[pid1].get(pid2);
		else {
			Set<CallOrSpawnStatement> systemCalls1 = this.enabledSystemCallMap
					.get(pid1);

			if (systemCalls1 != null && systemCalls1.size() == 1) {
				for (CallOrSpawnStatement call : systemCalls1) {
					SystemFunction systemFunction = (SystemFunction) call
							.function();
					if ((systemFunction.name().name().equals("$wait") || systemFunction
							.name().name().equals("$waitall"))
							&& systemFunction.getLibrary().equals("civlc")) {
						BitSet ampleSubSet;

						try {
							LibraryEnabler lib = enabler.libraryEnabler(
									call.getSource(),
									systemFunction.getLibrary());

							ampleSubSet = lib.ampleSet(state, pid1, call,
									this.reachablePtrWritable,
									this.reachablePtrReadonly,
									this.reachableNonPtrWritable,
									this.reachableNonPtrReadonly);
							this.waitMap[pid1] = ampleSubSet;
						} catch (LibraryLoaderException e) {
							throw new CIVLInternalException(
									"This is unreachable because the earlier execution "
											+ "has already checked that the library enabler "
											+ "gets loaded successfully otherwise an error should have been reported there",
									call.getSource());
						} catch (UnsatisfiablePathConditionException e) {
							return false;
						}
						if (ampleSubSet.get(pid2))
							return true;
					}
				}
			}
		}
		return false;
	}

	BitSet intersects(BitSet set1, BitSet set2) {
		BitSet result = new BitSet();

		for (int i = 0; i < set1.length(); i++) {
			i = set1.nextSetBit(i);
			if (set2.get(i))
				result.set(i);
		}
		return result;
	}

	// /**
	// * Given two collections of memory units, computes all the non-disjoint
	// * memory units from both collections. Two memory units are disjoint if
	// they
	// * don't share any common memory space. For example, <code>&a</code> and
	// * <code>&b</code> are disjoint if <code>a</code> and <code>b</code> are
	// * variables; <code>&a[0]</code> and <code>&a</code> are not disjoint
	// * because the latter contains the former.
	// *
	// * @param memSet1
	// * The first memory unit set.
	// * @param memSet2
	// * The second memory unit set.
	// * @return All non-disjoint memory units from the specified two sets.
	// */
	// private List<Pair<SymbolicExpression, SymbolicExpression>>
	// commonMemUnitPairs(
	// Iterable<SymbolicExpression> memSet1,
	// Iterable<SymbolicExpression> memSet2) {
	// List<Pair<SymbolicExpression, SymbolicExpression>> result = new
	// LinkedList<>();
	//
	// for (SymbolicExpression unit1 : memSet1) {
	// // ReferenceExpression myRef = symbolicUtil.getSymRef(unit1);
	// // SymbolicExpression unit1Obj = unit1;
	// //
	// // if (!myRef.isIdentityReference()) {
	// // unit1Obj = universe.tupleWrite(unit1, universe.intObject(2),
	// // universe.identityReference());
	// // }
	// for (SymbolicExpression unit2 : memSet2) {
	// if (!evaluator.symbolicUtility().isDisjointWith(unit1, unit2)) {
	// result.add(new Pair<>(unit1, unit2));
	// }
	// }
	// }
	// return result;
	// }

	/**
	 * Computes active processes at the current state, i.e., non-null processes
	 * with non-empty stack that have at least one enabled statements.
	 */
	private void computeActiveProcesses() {
		this.newGuardMap = new HashMap<>();
		for (ProcessState p : state.getProcessStates()) {
			boolean active = false;
			int pid;
			Map<Statement, SymbolicExpression> myGuards = new HashMap<>();

			if (p == null || p.hasEmptyStack())
				continue;

			pid = p.getPid();
			this.nonEmptyProcesses.set(pid);
			for (Statement s : p.getLocation().outgoing()) {
				SymbolicExpression myGuard;

				if (this.procBound > 0 && s instanceof CallOrSpawnStatement
						&& ((CallOrSpawnStatement) s).isSpawn()
						&& state.numLiveProcs() >= this.procBound)
					continue;
				myGuard = enabler.getGuard(s, pid, state).value;
				if (!myGuard.isFalse()) {
					myGuards.put(s, myGuard);
					active = true;
					break;
				}
			}
			if (active) {
				activeProcesses.set(pid);
				this.newGuardMap.put(pid, myGuards);
			}
		}
	}

	/**
	 * Computes the impact memory units of a certain process at the current
	 * state, which are usually decided by the variables appearing in the
	 * statements (including guards) originating at the process's current
	 * location. The computation could be incomplete when there is atomic/atom
	 * block that contains function calls.
	 * 
	 * @param proc
	 *            The process whose impact memory units are to be computed.
	 * @return The impact memory units of the process and the status to denote
	 *         if the computation is complete.
	 */
	// private Pair<MemoryUnitsStatus, Set<SymbolicExpression>>
	// impactMemoryUnits(
	// ProcessState proc) {
	// Set<SymbolicExpression> memUnits = new HashSet<>();
	// int pid = proc.getPid();
	// Location pLocation = proc.getLocation();
	// Pair<MemoryUnitsStatus, Set<SymbolicExpression>> partialResult;
	// Pair<MemoryUnitsStatus, Set<SymbolicExpression>> result = null;
	//
	// // this.enabledSystemCallMap.put(pid, new
	// // HashSet<CallOrSpawnStatement>());
	// if (debugging)
	// debugOut.println("impact memory units of " + proc.name() + "(id="
	// + proc.getPid() + "):");
	// if (pLocation.enterAtom() || pLocation.enterAtomic()
	// || proc.atomicCount() > 0)
	// // special handling of atomic blocks
	// result = impactMemoryUnitsOfAtomicFragment(pLocation, pid);
	// else {
	// for (Statement s : pLocation.outgoing()) {
	// try {
	// partialResult = impactMemoryUnitsOfStatement(s, pid);
	// if (partialResult.left == MemoryUnitsStatus.INCOMPLETE) {
	// result = partialResult;
	// break;
	// }
	// memUnits.addAll(partialResult.right);
	// } catch (UnsatisfiablePathConditionException e) {
	// continue;
	// }
	// }
	// }
	// if (result == null)
	// result = new Pair<>(MemoryUnitsStatus.NORMAL, memUnits);
	// if (debugging)
	// if (result.left == MemoryUnitsStatus.INCOMPLETE)
	// debugOut.println("INCOMPLETE");
	// else {
	// CIVLSource source = pLocation.getSource();
	//
	// for (SymbolicExpression memUnit : result.right) {
	// debugOut.print(symbolicAnalyzer.symbolicExpressionToString(
	// source, state, memUnit) + "\t");
	// }
	// debugOut.println();
	// }
	// return result;
	// }

	/**
	 * Computes the set of impact memory units of an atomic or atom block. All
	 * system function bodies are assumed to be independent (only the arguments
	 * are taken for computation). If there is any normal function calls, then
	 * the computation is terminated immediately and an empty set is returned
	 * with the INCOMPLETE status. This implementation is chosen because
	 * checking the impact memory units of function calls could be expensive and
	 * complicated and would be not worthy.
	 * 
	 * @param location
	 *            The start location of the atomic/atom block.
	 * @param pid
	 *            The ID of the current process.
	 * @return The set of impact memory units of the atomic/atom block and a
	 *         status variable to denote if the computation can be done
	 *         completely.
	 */
	private MemoryUnitSet impactMemoryUnitsOfAtomicFragment(Location location,
			int pid) {
		int atomicCount = state.getProcessState(pid).atomicCount();
		Set<CallOrSpawnStatement> systemCalls = new HashSet<>();
		BitSet checkedLocationIDs = new BitSet();
		Stack<Location> workings = new Stack<Location>();
		// Set<SymbolicExpression> memUnits = new HashSet<>();
		MemoryUnitSet muSet = this.memUnitFactory.newMemoryUnitSet();

		assert atomicCount > 0;
		workings.add(location);
		// DFS searching for reachable statements inside the $atomic/$atom
		// block
		while (!workings.isEmpty()) {
			Location currentLocation = workings.pop();
			Set<MemoryUnitExpression> impactMemUnitExprs = currentLocation
					.impactMemUnits();

			if (impactMemUnitExprs == null)
				return null;
			checkedLocationIDs.set(currentLocation.id());
			if (currentLocation.enterAtomic())
				atomicCount++;
			if (currentLocation.leaveAtomic())
				atomicCount--;
			if (atomicCount == 0 && !currentLocation.enterAtomic()) {
				atomicCount++;
				continue;
			}
			systemCalls.addAll(currentLocation.systemCalls());
			for (MemoryUnitExpression memUnitExpr : impactMemUnitExprs) {
				try {
					muSet = this.memUnitEvaluator.evaluates(state, pid,
							memUnitExpr, muSet);
				} catch (UnsatisfiablePathConditionException e) {
					// do nothing
				}
			}
			for (Statement statement : currentLocation.outgoing()) {
				if (statement.target() != null) {
					if (!checkedLocationIDs.get(statement.target().id())) {
						workings.push(statement.target());
					}
				}
			}
		}
		this.enabledSystemCallMap.put(pid, systemCalls);
		return muSet;
	}

	private MemoryUnitSet impactMemoryUnitsOfProcess(int pid) {
		Location location = state.getProcessState(pid).getLocation();
		Set<MemoryUnitExpression> impactMemUnitExprs = location
				.impactMemUnits();
		MemoryUnitSet impactMemUnits = this.memUnitFactory.newMemoryUnitSet();

		if (state.getProcessState(pid).atomicCount() > 0)
			return this.impactMemoryUnitsOfAtomicFragment(location, pid);
		if (impactMemUnitExprs == null)
			return null;
		this.enabledSystemCallMap.put(pid, location.systemCalls());
		for (MemoryUnitExpression memUnitExpr : impactMemUnitExprs) {
			// Set<SymbolicExpression> subResult = new HashSet<>();

			try {
				impactMemUnits = this.memUnitEvaluator.evaluates(state, pid,
						memUnitExpr, impactMemUnits);
			} catch (UnsatisfiablePathConditionException e) {
				// do nothing
			}
			// impactMemUnits.addAll(subResult);
		}
		return impactMemUnits;
	}

	/**
	 * Computes the impact memory units of a given statement of a certain
	 * process at the current state.
	 * 
	 * @param statement
	 *            The statement whose impact memory units are to be computed.
	 * @param pid
	 *            The id of the process that owns the statement.
	 * @return the impact memory units of the statement
	 * @throws UnsatisfiablePathConditionException
	 */
	/**
	 * Computes the set of memory units accessed by a given expression of a
	 * certain process at the current state.
	 * 
	 * @param expression
	 *            The expression whose impact memory units are to be computed.
	 * @param pid
	 *            The id of the process that the expression belongs to.
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */

	/**
	 * Pre-processing for ample set computation, including:
	 * <ul>
	 * <li>Computes the impact memory units for each process; and</li>
	 * <li>Computes the reachable memory units for each process.</li>
	 * </ul>
	 */
	private void preprocessing() {
		this.waitMap = new BitSet[state.numProcs()];
		if (debugging) {
			debugOut.println("===============memory analysis at state "
					+ state.getCanonicId() + "================");
		}
		reachableMemoryAnalysis();
		for (int pid = 0; pid < nonEmptyProcesses.length(); pid++) {
			pid = nonEmptyProcesses.nextSetBit(pid);
			// reachableMemoryUnits = state.getReachableMemUnitsWoPointer(pid);
			// reachableMemoryUnits.putAll(state
			// .getReachableMemUnitsWtPointer(pid));
			// impactMemUnitsMap.put(pid, this.impactMemoryUnitsOfProcess(pid));
			this.impactMemUnits[pid] = this.impactMemoryUnitsOfProcess(pid);
			// reachableMemUnitsMap.put(pid, reachableMemoryUnits);
			if (debugging) {
				debugOut.println("impact memory units of process " + pid + ":");
				this.impactMemUnits[pid].print(debugOut);
				debugOut.println();
				// debugOut.println("reachable memory units of process " + pid
				// + ":");
				// for (Map.Entry<SymbolicExpression, Boolean> entry :
				// this.reachableMemUnitsMap
				// .get(pid).entrySet()) {
				// debugOut.print(entry.getKey());
				// if (entry.getValue())
				// debugOut.print(" (w)");
				// debugOut.print("\t");
				// }
				// debugOut.println();
			}
		}
		if (debugging) {
			// enabler.stateFactory.;
			this.printReachableMemoryUnits();
		}
	}

	/**
	 * Given a process, computes the set of reachable memory units and if the
	 * memory unit could be modified at the current location or any future
	 * location.
	 * 
	 * @param proc
	 *            The process whose reachable memory units are to be computed.
	 * @return A map of reachable memory units and if they could be modified by
	 *         the process. //
	 */
	// private Map<SymbolicExpression, Boolean> reachableMemoryUnits(
	// ProcessState proc) {
	// Set<Integer> checkedDyScopes = new HashSet<>();
	// Map<SymbolicExpression, Boolean> memUnitPermissionMap = new HashMap<>();
	// Set<Variable> writableVariables = proc.getLocation()
	// .writableVariables();
	// // only look at the top stack is sufficient
	// StackEntry callStack = proc.peekStack();
	// int dyScopeID = callStack.scope();
	// String process = "p" + proc.identifier() + " (id = " + proc.getPid()
	// + ")";
	//
	// if (debugging)
	// debugOut.println("reachable memory units of " + proc.name()
	// + "(id=" + proc.getPid() + "):");
	// while (dyScopeID >= 0) {
	// if (checkedDyScopes.contains(dyScopeID))
	// break;
	// else {
	// DynamicScope dyScope = state.getDyscope(dyScopeID);
	// int size = dyScope.numberOfValues();
	//
	// for (int vid = 0; vid < size; vid++) {
	// Variable variable = dyScope.lexicalScope().variable(vid);
	// Set<SymbolicExpression> varMemUnits;
	// boolean permission;
	//
	// // ignore the heap
	// if (variable.type().isHeapType())// && vid != 0)
	// continue;
	// if (variable.hasPointerRef())
	// varMemUnits = evaluator
	// .memoryUnitsReachableFromVariable(
	// variable.type(), dyScope.getValue(vid),
	// dyScopeID, vid, state, process);
	// else {
	// varMemUnits = new HashSet<SymbolicExpression>(1);
	// varMemUnits.add(evaluator.symbolicUtility()
	// .makePointer(
	// dyScopeID,
	// vid,
	// evaluator.universe()
	// .identityReference()));
	// }
	// permission = writableVariables.contains(variable) ? true
	// : false;
	// for (SymbolicExpression unit : varMemUnits) {
	// if (!memUnitPermissionMap.containsKey(unit)) {
	// memUnitPermissionMap.put(unit, permission);
	// }
	// }
	// }
	// checkedDyScopes.add(dyScopeID);
	// dyScopeID = state.getParentId(dyScopeID);
	// }
	// }
	// if (debugging) {
	// CIVLSource source = proc.getLocation().getSource();
	//
	// for (SymbolicExpression memUnit : memUnitPermissionMap.keySet()) {
	// debugOut.print(symbolicAnalyzer.symbolicExpressionToString(
	// source, state, memUnit));
	// debugOut.print("(");
	// if (memUnitPermissionMap.get(memUnit))
	// debugOut.print("W");
	// else
	// debugOut.print("R");
	// debugOut.print(")\t");
	// }
	// debugOut.println();
	// }
	// return memUnitPermissionMap;
	// }

	private void printReachableMemoryUnits() {
		for (int i = 0; i < state.numProcs(); i++) {
			ProcessState proc = state.getProcessState(i);
			// ImmutableState theState = (ImmutableState) state;

			if (proc == null || proc.hasEmptyStack())
				continue;
			debugOut.println("reachable memory units (non-ptr, readonly) of process "
					+ i + ":");
			reachableNonPtrReadonly[i].print(debugOut);
			debugOut.println();
			debugOut.println("reachable memory units (non-ptr, writable) of process "
					+ i + ":");
			reachableNonPtrWritable[i].print(debugOut);
			debugOut.println();
			debugOut.println("reachable memory units (ptr, readonly) of process "
					+ i + ":");
			reachablePtrReadonly[i].print(debugOut);
			debugOut.println();
			debugOut.println("reachable memory units (ptr, writable) of process "
					+ i + ":");
			reachablePtrWritable[i].print(debugOut);
			debugOut.println();
		}
	}

	private void reachableMemoryAnalysis() {
		int numProcs = state.numProcs();
		ReferenceExpression identity = universe.identityReference();

		this.reachableNonPtrReadonly = new MemoryUnitSet[numProcs];
		this.reachableNonPtrWritable = new MemoryUnitSet[numProcs];
		this.reachablePtrReadonly = new MemoryUnitSet[numProcs];
		this.reachablePtrWritable = new MemoryUnitSet[numProcs];
		for (int pid = 0; pid < numProcs; pid++) {
			Set<Variable> writableVars = new HashSet<>();
			ProcessState process = state.getProcessState(pid);
			Set<MemoryUnitExpression> reachableNonPtrExpr = new HashSet<>(), reachablePtrExpr = new HashSet<>();
			MemoryUnitSet nonPtrReadonly = memUnitFactory.newMemoryUnitSet(), nonPtrWritable = memUnitFactory
					.newMemoryUnitSet(), ptrReadonly = memUnitFactory
					.newMemoryUnitSet(), ptrWritable = memUnitFactory
					.newMemoryUnitSet();

			if (process != null && !process.hasEmptyStack())
				for (StackEntry call : process.getStackEntries()) {
					Location location = call.location();

					writableVars.addAll(location.writableVariables());
					for (MemoryUnitExpression memUnit : location
							.reachableMemUnitsWtPointer()) {
						if (memUnit.writable())
							reachablePtrExpr.remove(memUnit);
						reachablePtrExpr.add(memUnit);
					}
					for (MemoryUnitExpression memUnit : location
							.reachableMemUnitsWoPointer()) {
						if (memUnit.writable())
							reachableNonPtrExpr.remove(memUnit);
						reachableNonPtrExpr.add(memUnit);
					}
				}
			for (MemoryUnitExpression memUnitExpr : reachablePtrExpr) {
				int dyscopeID = state.getDyscope(pid, memUnitExpr.scopeId());
				int varID = memUnitExpr.variableId();
				MemoryUnit mu = memUnitFactory.newMemoryUnit(dyscopeID, varID,
						identity);
				SymbolicExpression varValue = state.getVariableValue(dyscopeID,
						varID);

				if (writableVars.contains(memUnitExpr.variable())) {
					// ptrWritable =
					memUnitFactory.add(ptrWritable, mu);
					// ptrWritable =
					findPointersInExpression(varValue, ptrWritable, state);
				} else {
					// ptrReadonly =
					memUnitFactory.add(ptrReadonly, mu);
					// ptrReadonly =
					findPointersInExpression(varValue, ptrReadonly, state);
				}
			}
			for (MemoryUnitExpression memUnitExpr : reachableNonPtrExpr) {
				int dyscopeID = state.getDyscope(pid, memUnitExpr.scopeId());
				int varID = memUnitExpr.variableId();
				MemoryUnit mu = memUnitFactory.newMemoryUnit(dyscopeID, varID,
						identity);
				Variable variable = memUnitExpr.variable();

				if (variable.type().isHandleType()) {
					SymbolicExpression value = state.getVariableValue(
							dyscopeID, varID);
					CIVLSource source = variable.getSource();

					if (!value.isNull() && symbolicUtil.isValidPointer(value))
						memUnitFactory.add(nonPtrReadonly, memUnitFactory
								.newMemoryUnit(symbolicUtil.getDyscopeId(
										source, value), symbolicUtil
										.getVariableId(source, value),
										symbolicUtil.getSymRef(value)));
				}
				if (writableVars.contains(memUnitExpr.variable()))
					memUnitFactory.add(nonPtrWritable, mu);
				else
					memUnitFactory.add(nonPtrReadonly, mu);
			}
			reachableNonPtrReadonly[pid] = nonPtrReadonly;
			reachableNonPtrWritable[pid] = nonPtrWritable;
			reachablePtrReadonly[pid] = ptrReadonly;
			reachablePtrWritable[pid] = ptrWritable;
		}
	}

	private boolean hasAccessConflict(int thisPid, int thatPid, MemoryUnit mu) {
		MemoryUnitSet reachablePtrWritableThat = this.reachablePtrWritable[thatPid];
		MemoryUnitSet reachablePtrReadonlyThat = this.reachablePtrReadonly[thatPid];
		MemoryUnitSet reachableNonPtrWritableThat = this.reachableNonPtrWritable[thatPid];
		MemoryUnitSet reachableNonPtrReadonlyThat = this.reachableNonPtrReadonly[thatPid];
		MemoryUnitSet reachablePtrWritableThis = this.reachablePtrWritable[thisPid];
		MemoryUnitSet reachablePtrReadonlyThis = this.reachablePtrReadonly[thisPid];
		MemoryUnitSet reachableNonPtrWritableThis = this.reachableNonPtrWritable[thisPid];
		MemoryUnitSet reachableNonPtrReadonlyThis = this.reachableNonPtrReadonly[thisPid];
		boolean thisRead = false, thisWrite = false, thatRead = false, thatWrite = false;

		if (memUnitFactory.isJoint(reachablePtrWritableThis, mu)
				|| memUnitFactory.isJoint(reachableNonPtrWritableThis, mu))
			thisWrite = true;
		else if (memUnitFactory.isJoint(reachablePtrReadonlyThis, mu)
				|| memUnitFactory.isJoint(reachableNonPtrReadonlyThis, mu))
			thisRead = true;
		if (memUnitFactory.isJoint(reachablePtrWritableThat, mu)
				|| memUnitFactory.isJoint(reachableNonPtrWritableThat, mu))
			thatWrite = true;
		else if (memUnitFactory.isJoint(reachablePtrReadonlyThat, mu)
				|| memUnitFactory.isJoint(reachableNonPtrReadonlyThat, mu))
			thatRead = true;
		if ((thisWrite && thatRead) || (thisRead && thatWrite)
				|| (thisWrite && thatWrite))
			return true;
		return false;
	}

	/**
	 * Finds pointers contained in a given expression recursively.
	 * 
	 * @param expr
	 * @param set
	 * @param state
	 */
	private void findPointersInExpression(SymbolicExpression expr,
			MemoryUnitSet muSet, State state) {
		SymbolicType type = expr.type();
		MemoryUnitSet result = muSet;

		// TODO check comm type
		if (type != null && !type.equals(modelFactory.heapSymbolicType())
				&& !type.equals(modelFactory.bundleSymbolicType())) {
			// need to eliminate heap type as well. each proc has its own.
			if (modelFactory.pointerSymbolicType().equals(type)) {
				SymbolicExpression pointerValue;
				SymbolicExpression eval;
				Variable variable;

				if (!symbolicUtil.isValidPointer(expr))
					return;
				variable = state
						.getDyscope(symbolicUtil.getDyscopeId(null, expr))
						.lexicalScope()
						.variable(symbolicUtil.getVariableId(null, expr));
				if (variable.isConst() || variable.isInput())
					return;
				// result =
				this.memUnitFactory.add(result, expr);
				if (expr.operator() == SymbolicOperator.CONCRETE) {
					/*
					 * If the expression is an arrayElementReference expression,
					 * and finally it turns that the array type has length 0,
					 * return immediately. Because we can not dereference it and
					 * the dereference exception shouldn't report here.
					 */
					if (symbolicUtil.getSymRef(expr).isArrayElementReference()) {
						SymbolicExpression arrayPointer = symbolicUtil
								.parentPointer(null, expr);

						eval = this.dereference(state, arrayPointer);
						/* Check if it's length == 0 */
						if (universe.length(eval).isZero())
							return;
					}
					pointerValue = this.dereference(state, expr);
					// TODO what's this?
					if (pointerValue == null)
						return;
					if (pointerValue.operator() == SymbolicOperator.CONCRETE
							&& pointerValue.type() != null
							&& pointerValue.type().equals(
									modelFactory.pointerSymbolicType()))
						findPointersInExpression(pointerValue, result, state);
				}
			} else {
				int numArgs = expr.numArguments();

				for (int i = 0; i < numArgs; i++) {
					SymbolicObject arg = expr.argument(i);

					findPointersInObject(arg, result, state);
				}
			}
		}
		return;
	}

	/**
	 * Finds all the pointers that can be dereferenced inside a symbolic object.
	 * 
	 * @param object
	 *            a symbolic object
	 * @param set
	 *            a set to which the pointer values will be added
	 * @param heapType
	 *            the heap type, which will be ignored
	 */
	private void findPointersInObject(SymbolicObject object,
			MemoryUnitSet muSet, State state) {
		switch (object.symbolicObjectKind()) {
		case EXPRESSION: {
			findPointersInExpression((SymbolicExpression) object, muSet, state);
			return;
		}
		case EXPRESSION_COLLECTION: {
			MemoryUnitSet result = muSet;

			for (SymbolicExpression expr : (SymbolicCollection<?>) object)
				findPointersInExpression(expr, result, state);

			return;
		}
		default:
			// ignore types and primitives, they don't have any pointers
			// you can dereference.
		}
		return;
	}

	/**
	 * 
	 * @param state
	 * @param pointer
	 * @return
	 */
	private SymbolicExpression dereference(State state,
			SymbolicExpression pointer) {
		int sid = symbolicUtil.getDyscopeId(null, pointer);
		int vid = symbolicUtil.getVariableId(null, pointer);
		ReferenceExpression symRef = symbolicUtil.getSymRef(pointer);
		SymbolicExpression variableValue;
		SymbolicExpression deref;

		variableValue = state.getDyscope(sid).getValue(vid);
		try {
			deref = universe.dereference(variableValue, symRef);
		} catch (SARLException e) {
			return null;
		}
		return deref;
	}

}
