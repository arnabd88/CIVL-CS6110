package edu.udel.cis.vsl.civl.kripke.common;

import java.io.PrintStream;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import edu.udel.cis.vsl.civl.kripke.IF.LibraryEnabler;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.SystemFunction;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.AssertStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.AssignStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.AssumeStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.MallocStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ReturnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.statement.StatementList;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryLoaderException;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.DynamicScope;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.StackEntry;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * This class is responsible for computing the ample processes set at a given
 * state. It is a helper of Enabler.
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
	private enum MemoryUnitsStatus {
		NORMAL, INCOMPLETE
	};

	/* *************************** Instance Fields ************************* */

	Set<Integer> allProcesses = new LinkedHashSet<>();

	/**
	 * The map of active processes (i.e., non-null processes with non-empty
	 * stack that have at least one enabled statement)
	 */
	Set<Integer> activeProcesses = new LinkedHashSet<>();

	/**
	 * The unique enabler used in the system. Used here for evaluating the guard
	 * of statements.
	 */
	private CommonEnabler enabler;

	/**
	 * The unique evaluator of the system. Used to evaluate expressions and
	 * variables for calculating impact or reachable memory units and so on.
	 */
	private Evaluator evaluator;

	/**
	 * Turn on/off the printing of debugging information for the ample set
	 * algorithm.
	 */
	private boolean debugging = false;

	/**
	 * The output stream used for debugging.
	 */
	private PrintStream debugOut = System.out;

	/**
	 * map of process ID's and their impact memory units (NULL impact memory
	 * units means that the computation is incomplete and all active processes
	 * should be included in the ample set)
	 */
	Map<Integer, Set<SymbolicExpression>> impactMemUnitsMap = new HashMap<>();

	/**
	 * map of process ID's and their reachable memory units with information
	 * that whether the memory unit is to be written.
	 */
	Map<Integer, Map<SymbolicExpression, Boolean>> reachableMemUnitsMap = new HashMap<>();

	/**
	 * map of communicators and the sets of process ID's with different ranks of
	 * the communicator
	 */
	Map<SymbolicExpression, Map<Integer, Set<Integer>>> processesInCommMap = new HashMap<>();

	/**
	 * map of process ID's and its rank id in each communicator.
	 */
	Map<Integer, Map<SymbolicExpression, Integer>> processRankMap = new HashMap<>();

	/**
	 * map of process ID's and the set of enabled system call statements.
	 */
	Map<Integer, Set<CallOrSpawnStatement>> enabledSystemCallMap = new HashMap<>();

	/**
	 * The current state at which the ample set is to be computed.
	 */
	private State state;

	private SymbolicAnalyzer symbolicAnalyzer;

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
			SymbolicAnalyzer symbolicAnalyzer, boolean debug,
			PrintStream debugOut) {
		this.state = state;
		this.enabler = enabler;
		this.evaluator = evaluator;
		this.symbolicAnalyzer = symbolicAnalyzer;
		this.debugging = debug;
		this.debugOut = debugOut;
	}

	/* *********************** Package-private Methods ********************* */

	/**
	 * Obtains the set of ample processes for the current state.
	 * 
	 * @return
	 */
	Set<ProcessState> ampleProcesses() {
		Set<Integer> ampleProcessIDs;
		Set<ProcessState> ampleProcesses = new LinkedHashSet<>();

		// process and if it contains any comm_enque or comm_deque call
		computeActiveProcesses();
		// return immediately if at most one process is activated.
		if (activeProcesses.size() <= 1)
			ampleProcessIDs = activeProcesses;
		else {
			ampleProcessIDs = ampleProcessesWork();
		}
		for (int pid : ampleProcessIDs) {
			ampleProcesses.add(state.getProcessState(pid));
		}
		return ampleProcesses;
	}

	/* *************************** Private Methods ************************* */

	/**
	 * Compute the ample set when there are more than one active processes.
	 * 
	 * @return The set of process ID's to be contained in the ample set.
	 */
	private Set<Integer> ampleProcessesWork() {
		Set<Integer> result = new LinkedHashSet<>();
		int minimalAmpleSetSize = activeProcesses.size() + 1;

		preprocessing();
		for (int pid : activeProcesses) {
			Set<Integer> ampleSet = ampleSetOfProcess(pid, minimalAmpleSetSize);
			int currentSize = ampleSet.size();

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
	 * Compute the ample set starting with a specific process.
	 * 
	 * @param startPid
	 *            The id of the process to start with.
	 * @return The set of process ID's to be contained in the ample set.
	 */
	private Set<Integer> ampleSetOfProcess(int startPid, int minAmpleSize) {
		Set<Integer> ampleProcessIDs = new LinkedHashSet<>();
		Stack<Integer> workingProcessIDs = new Stack<>();
		int myAmpleSetActiveSize = 1;

		workingProcessIDs.add(startPid);
		ampleProcessIDs.add(startPid);
		while (!workingProcessIDs.isEmpty()) {
			int pid = workingProcessIDs.pop();
			Set<SymbolicExpression> impactMemUnits = impactMemUnitsMap.get(pid);
			Map<SymbolicExpression, Boolean> reachableMemUnitsMapOfThis = reachableMemUnitsMap
					.get(pid);
			Set<CallOrSpawnStatement> systemCalls = this.enabledSystemCallMap
					.get(pid);

			if (impactMemUnits == null) {
				// The current process is entering an atomic/atom block
				// whose impact memory units can't be computed
				// completely
				ampleProcessIDs = activeProcesses;
				return ampleProcessIDs;
			}
			if (systemCalls != null && !systemCalls.isEmpty()) {
				for (CallOrSpawnStatement call : systemCalls) {
					SystemFunction systemFunction = (SystemFunction) call
							.function();
					Set<Integer> ampleSubSet = null;

					try {
						LibraryEnabler lib = enabler.libraryEnabler(
								call.getSource(), systemFunction.getLibrary());

						ampleSubSet = lib.ampleSet(state, pid, call,
								reachableMemUnitsMap);
					} catch (LibraryLoaderException e) {
						throw new CIVLInternalException(
								"This is unreachable because the earlier execution "
										+ "has already checked that the library enabler "
										+ "gets loaded successfully otherwise an error should have been reported there",
								call.getSource());
					} catch (UnsatisfiablePathConditionException e) {
						ampleProcessIDs = activeProcesses;
						return ampleProcessIDs;
					}
					if (ampleSubSet != null && !ampleSubSet.isEmpty()) {
						for (int amplePid : ampleSubSet) {
							if (amplePid != pid
									// && activeProcesses.contains(amplePid)
									&& !ampleProcessIDs.contains(amplePid)
									&& !workingProcessIDs.contains(amplePid)) {

								workingProcessIDs.add(amplePid);
								ampleProcessIDs.add(amplePid);
								if (this.activeProcesses.contains(amplePid))
									myAmpleSetActiveSize++;
								// early return
								if (myAmpleSetActiveSize >= minAmpleSize
										|| myAmpleSetActiveSize == activeProcesses
												.size()) {
									ampleProcessIDs.retainAll(activeProcesses);
									return ampleProcessIDs;
								}
							}
						}
					}
				}
			}
			for (int otherPid : this.allProcesses) {
				Map<SymbolicExpression, Boolean> reachableMemUnitsMapOfOther;
				List<Pair<SymbolicExpression, SymbolicExpression>> sharedMemUnitPairs;

				// add new ample id earlier
				if (otherPid == pid || ampleProcessIDs.contains(otherPid)
						|| workingProcessIDs.contains(otherPid))
					continue;
				reachableMemUnitsMapOfOther = reachableMemUnitsMap
						.get(otherPid);
				sharedMemUnitPairs = this.memUnitPairs(impactMemUnits,
						reachableMemUnitsMapOfOther.keySet());
				for (Pair<SymbolicExpression, SymbolicExpression> memPair : sharedMemUnitPairs) {
					if ((reachableMemUnitsMapOfThis.get(memPair.left) || reachableMemUnitsMapOfOther
							.get(memPair.right))) {
						workingProcessIDs.add(otherPid);
						ampleProcessIDs.add(otherPid);
						if (this.activeProcesses.contains(otherPid))
							myAmpleSetActiveSize++;
						break;
					}
				}
				// early return
				if (myAmpleSetActiveSize >= minAmpleSize
						|| myAmpleSetActiveSize == activeProcesses.size()) {
					ampleProcessIDs.retainAll(activeProcesses);
					return ampleProcessIDs;
				}
			}
		}
		ampleProcessIDs.retainAll(activeProcesses);
		return ampleProcessIDs;
	}

	private List<Pair<SymbolicExpression, SymbolicExpression>> memUnitPairs(
			Iterable<SymbolicExpression> list1,
			Iterable<SymbolicExpression> list2) {
		List<Pair<SymbolicExpression, SymbolicExpression>> result = new LinkedList<>();

		for (SymbolicExpression unit1 : list1) {
			for (SymbolicExpression unit2 : list2) {
				if (!evaluator.symbolicUtility().isDisjointWith(unit1, unit2))
					result.add(new Pair<>(unit1, unit2));
			}
		}
		return result;
	}

	/**
	 * Compute active processes at the current state, i.e., non-null processes
	 * with non-empty stack that have at least one enabled statements.
	 * 
	 */
	private void computeActiveProcesses() {
		for (ProcessState p : state.getProcessStates()) {
			boolean active = false;
			int pid;

			if (p == null || p.hasEmptyStack())
				continue;
			pid = p.getPid();
			this.allProcesses.add(pid);
			for (Statement s : p.getLocation().outgoing()) {
				if (!enabler.getGuard(s, pid, state).value.isFalse()) {
					active = true;
				}
			}
			if (active)
				activeProcesses.add(pid);
		}
	}

	/**
	 * The impact memory units of a certain process at the current state. The
	 * computation could be incomplete when there is atomic/atom block that
	 * contains function calls.
	 * 
	 * @param proc
	 *            The process whose impact memory units are to be computed.
	 * @return The impact memory units of the process and the status to denote
	 *         if the computation is complete.
	 */
	private Pair<MemoryUnitsStatus, Set<SymbolicExpression>> impactMemoryUnits(
			ProcessState proc) {
		Set<SymbolicExpression> memUnits = new HashSet<>();
		int pid = proc.getPid();
		Location pLocation = proc.getLocation();
		Pair<MemoryUnitsStatus, Set<SymbolicExpression>> partialResult;
		Pair<MemoryUnitsStatus, Set<SymbolicExpression>> result = null;

		this.enabledSystemCallMap.put(pid, new HashSet<CallOrSpawnStatement>());
		if (debugging)
			debugOut.println("impact memory units of " + proc.name() + "(id="
					+ proc.getPid() + "):");
		if (pLocation.enterAtom() || pLocation.enterAtomic()
				|| proc.atomicCount() > 0) {
			result = impactMemoryUnitsOfAtomicBlock(pLocation, pid);
		} else {
			for (Statement s : pLocation.outgoing()) {
				try {
					partialResult = impactMemoryUnitsOfStatement(s, pid);
					if (partialResult.left == MemoryUnitsStatus.INCOMPLETE) {
						result = partialResult;
						break;
					}
					memUnits.addAll(partialResult.right);
				} catch (UnsatisfiablePathConditionException e) {
					continue;
				}
			}
		}
		if (result == null)
			result = new Pair<>(MemoryUnitsStatus.NORMAL, memUnits);
		if (debugging)
			if (result.left == MemoryUnitsStatus.INCOMPLETE)
				debugOut.println("INCOMPLETE");
			else {
				CIVLSource source = pLocation.getSource();

				for (SymbolicExpression memUnit : result.right) {
					debugOut.print(symbolicAnalyzer.symbolicExpressionToString(
							source, state, memUnit) + "\t");
				}
				debugOut.println();
			}
		return result;
	}

	/**
	 * Compute the set of impact memory units of an atomic or atom block. All
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
	private Pair<MemoryUnitsStatus, Set<SymbolicExpression>> impactMemoryUnitsOfAtomicBlock(
			Location location, int pid) {
		int atomicCount = state.getProcessState(pid).atomicCount();
		Stack<Integer> atomFlags = new Stack<Integer>();
		Pair<MemoryUnitsStatus, Set<SymbolicExpression>> partialResult;

		if (atomicCount > 0) {
			for (int i = 0; i < atomicCount; i++) {
				atomFlags.push(1);
			}
		}
		if (atomicCount > 0 || location.enterAtom() || location.enterAtomic()) {
			Set<Integer> checkedLocations = new HashSet<Integer>();
			Stack<Location> workings = new Stack<Location>();
			Set<SymbolicExpression> memUnits = new HashSet<>();

			workings.add(location);
			// DFS searching for reachable statements inside the $atomic/$atom
			// block
			while (!workings.isEmpty()) {
				Location currentLocation = workings.pop();

				checkedLocations.add(currentLocation.id());
				if (location.enterAtom() && currentLocation.enterAtom())
					atomFlags.push(1);
				if (location.enterAtomic() && currentLocation.enterAtomic())
					atomFlags.push(1);
				if (location.enterAtom() && currentLocation.leaveAtom())
					atomFlags.pop();
				if (location.enterAtomic() && currentLocation.leaveAtomic())
					atomFlags.pop();
				if (atomFlags.isEmpty()) {
					if (location.enterAtom()) {
						if (!currentLocation.enterAtom())
							atomFlags.push(1);
					}
					if (location.enterAtomic()) {
						if (!currentLocation.enterAtomic())
							atomFlags.push(1);
					}
					continue;
				}
				if (currentLocation.getNumOutgoing() > 0) {
					int number = currentLocation.getNumOutgoing();
					for (int i = 0; i < number; i++) {
						Statement s = currentLocation.getOutgoing(i);

						if (s instanceof CallOrSpawnStatement) {
							CallOrSpawnStatement callOrSpawnStatement = (CallOrSpawnStatement) s;

							if (callOrSpawnStatement.isCall()) {
								return new Pair<MemoryUnitsStatus, Set<SymbolicExpression>>(
										MemoryUnitsStatus.INCOMPLETE, memUnits);
							}
						}
						try {
							partialResult = impactMemoryUnitsOfStatement(s, pid);
							if (partialResult.left == MemoryUnitsStatus.INCOMPLETE)
								return partialResult;
							memUnits.addAll(partialResult.right);
						} catch (UnsatisfiablePathConditionException e) {

						}
						if (s.target() != null) {
							if (!checkedLocations.contains(s.target().id())) {
								workings.push(s.target());
							}
						}
					}
				}
			}
			return new Pair<MemoryUnitsStatus, Set<SymbolicExpression>>(
					MemoryUnitsStatus.NORMAL, memUnits);
		}
		return null;
	}

	/**
	 * Compute the impact memory units of a given statement of a certain process
	 * at the current state.
	 * 
	 * @param statement
	 *            The statement whose impact memory units are to be computed.
	 * @param pid
	 *            The id of the process that owns the statement.
	 * @return the impact memory units of the statement
	 * @throws UnsatisfiablePathConditionException
	 */
	private Pair<MemoryUnitsStatus, Set<SymbolicExpression>> impactMemoryUnitsOfStatement(
			Statement statement, int pid)
			throws UnsatisfiablePathConditionException {
		Set<SymbolicExpression> memUnits = new HashSet<>();
		Pair<MemoryUnitsStatus, Set<SymbolicExpression>> partialResult = memoryUnit(
				statement.guard(), pid);
		Set<SymbolicExpression> memUnitsPartial = partialResult.right;

		if (partialResult.left == MemoryUnitsStatus.INCOMPLETE)
			return partialResult;
		if (memUnitsPartial != null) {
			memUnits.addAll(memUnitsPartial);
		}
		switch (statement.statementKind()) {
		case ASSIGN:
		case CHOOSE: {
			AssignStatement assignStatement = (AssignStatement) statement;

			partialResult = memoryUnit(assignStatement.getLhs(), pid);
			if (partialResult.left == MemoryUnitsStatus.INCOMPLETE)
				return partialResult;
			memUnitsPartial = partialResult.right;
			if (memUnitsPartial != null) {
				memUnits.addAll(memUnitsPartial);
			}
			partialResult = memoryUnit(assignStatement.rhs(), pid);
			if (partialResult.left == MemoryUnitsStatus.INCOMPLETE)
				return partialResult;
			memUnitsPartial = partialResult.right;
			if (memUnitsPartial != null) {
				memUnits.addAll(memUnitsPartial);
			}
		}
			break;
		case ASSUME: {
			AssumeStatement assumeStatement = (AssumeStatement) statement;
			Expression assumeExpression = assumeStatement.getExpression();

			partialResult = memoryUnit(assumeExpression, pid);
			if (partialResult.left == MemoryUnitsStatus.INCOMPLETE)
				return partialResult;
			memUnitsPartial = partialResult.right;
			if (memUnitsPartial != null) {
				memUnits.addAll(memUnitsPartial);
			}
		}
			break;
		case ASSERT: {
			AssertStatement assertStatement = (AssertStatement) statement;
			Expression assertExpression = assertStatement.getCondition();

			partialResult = memoryUnit(assertExpression, pid);
			if (partialResult.left == MemoryUnitsStatus.INCOMPLETE)
				return partialResult;
			memUnitsPartial = partialResult.right;
			if (memUnitsPartial != null) {
				memUnits.addAll(memUnitsPartial);
			}
		}
			break;
		case CALL_OR_SPAWN: {
			CallOrSpawnStatement call = (CallOrSpawnStatement) statement;

			if (call.isSystemCall()) {
				this.enabledSystemCallMap.get(pid).add(call);
			}
			for (Expression argument : call.arguments()) {
				partialResult = memoryUnit(argument, pid);
				if (partialResult.left == MemoryUnitsStatus.INCOMPLETE)
					return partialResult;
				memUnitsPartial = partialResult.right;
				if (memUnitsPartial != null) {
					memUnits.addAll(memUnitsPartial);
				}
			}
		}
			break;
		case MALLOC: {
			MallocStatement mallocStatement = (MallocStatement) statement;

			partialResult = memoryUnit(mallocStatement.getLHS(), pid);
			if (partialResult.left == MemoryUnitsStatus.INCOMPLETE)
				return partialResult;
			memUnitsPartial = partialResult.right;
			if (memUnitsPartial != null) {
				memUnits.addAll(memUnitsPartial);
			}
			partialResult = memoryUnit(mallocStatement.getScopeExpression(),
					pid);
			if (partialResult.left == MemoryUnitsStatus.INCOMPLETE)
				return partialResult;
			memUnitsPartial = partialResult.right;
			if (memUnitsPartial != null) {
				memUnits.addAll(memUnitsPartial);
			}
			partialResult = memoryUnit(mallocStatement.getSizeExpression(), pid);
			if (partialResult.left == MemoryUnitsStatus.INCOMPLETE)
				return partialResult;
			memUnitsPartial = partialResult.right;
			if (memUnitsPartial != null) {
				memUnits.addAll(memUnitsPartial);
			}
		}
			break;
		case NOOP:
			break;
		case RETURN: {
			ReturnStatement returnStatement = (ReturnStatement) statement;

			if (returnStatement.expression() != null) {
				partialResult = memoryUnit(returnStatement.expression(), pid);
				if (partialResult.left == MemoryUnitsStatus.INCOMPLETE)
					return partialResult;
				memUnitsPartial = partialResult.right;
				if (memUnitsPartial != null) {
					memUnits.addAll(memUnitsPartial);
				}
			}
		}
			break;
		case STATEMENT_LIST: {
			StatementList statementList = (StatementList) statement;

			for (Statement subStatement : statementList.statements()) {
				partialResult = impactMemoryUnitsOfStatement(subStatement, pid);
				if (partialResult.left == MemoryUnitsStatus.INCOMPLETE)
					return partialResult;
				memUnits.addAll(memUnitsPartial);
			}
		}
			break;
		case CIVL_FOR_ENTER:
			break;
		default:
			throw new CIVLUnimplementedFeatureException(
					"Impact memory units for statement: ", statement);
		}

		return new Pair<>(MemoryUnitsStatus.NORMAL, memUnits);
	}

	/**
	 * Compute the set of memory units accessed by a given expression of a
	 * certain process at the current state.
	 * 
	 * @param expression
	 *            The expression whose impact memory units are to be computed.
	 * @param pid
	 *            The id of the process that the expression belongs to.
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Pair<MemoryUnitsStatus, Set<SymbolicExpression>> memoryUnit(
			Expression expression, int pid)
			throws UnsatisfiablePathConditionException {
		Set<SymbolicExpression> memoryUnits = new HashSet<>();
		MemoryUnitsStatus status;

		evaluator.memoryUnitsOfExpression(state, pid, expression, memoryUnits);
		// TODO get rid of status.
		status = MemoryUnitsStatus.NORMAL;
		// if (debugging) {
		// printMemoryUnitsOfExpression(expression, memoryUnits);
		// }
		return new Pair<>(status, memoryUnits);
	}

	/**
	 * Pre-processing for ample set computation, including:
	 * <ul>
	 * <li>Compute the impact memory units for each process; and</li>
	 * <li>Compute the reachable memory units for each process.</li>
	 * </ul>
	 */
	private void preprocessing() {
		for (int pid : allProcesses) {
			ProcessState p = state.getProcessState(pid);

			Pair<MemoryUnitsStatus, Set<SymbolicExpression>> impactMemUnitsPair = impactMemoryUnits(p);

			if (impactMemUnitsPair.left == MemoryUnitsStatus.INCOMPLETE) {
				impactMemUnitsMap.put(pid, null);
			} else {
				impactMemUnitsMap.put(pid, impactMemUnitsPair.right);
			}
			reachableMemUnitsMap.put(pid, reachableMemoryUnits(p));
		}
	}

	/**
	 * Given a process, compute the set of reachable memory units and if the
	 * memory unit could be modified at the current location or any future
	 * location.
	 * 
	 * @param proc
	 *            The process whose reachable memory units are to be computed.
	 * @return A map of reachable memory units and if they could be modified by
	 *         the process.
	 */
	private Map<SymbolicExpression, Boolean> reachableMemoryUnits(
			ProcessState proc) {
		Set<Integer> checkedDyScopes = new HashSet<>();
		Map<SymbolicExpression, Boolean> memUnitPermissionMap = new HashMap<>();
		Set<Variable> writableVariables = proc.getLocation()
				.writableVariables();
		// only look at the top stack is sufficient
		StackEntry callStack = proc.peekStack();
		int dyScopeID = callStack.scope();
		String process = "p" + proc.identifier() + " (id = " + proc.getPid()
				+ ")";

		if (debugging)
			debugOut.println("reachable memory units of " + proc.name()
					+ "(id=" + proc.getPid() + "):");
		while (dyScopeID >= 0) {
			if (checkedDyScopes.contains(dyScopeID))
				break;
			else {
				DynamicScope dyScope = state.getDyscope(dyScopeID);
				int size = dyScope.numberOfValues();

				for (int vid = 0; vid < size; vid++) {
					Variable variable = dyScope.lexicalScope().variable(vid);
					Set<SymbolicExpression> varMemUnits;
					boolean permission;

					if (variable.type().isHeapType() && vid != 0)
						continue;
					varMemUnits = evaluator.memoryUnitsReachableFromVariable(
							variable.type(), dyScope.getValue(vid), dyScopeID,
							vid, state, process);
					permission = writableVariables.contains(variable) ? true
							: false;
					for (SymbolicExpression unit : varMemUnits) {
						if (!memUnitPermissionMap.containsKey(unit)) {
							memUnitPermissionMap.put(unit, permission);
						}
					}
				}
				checkedDyScopes.add(dyScopeID);
				dyScopeID = state.getParentId(dyScopeID);
			}
		}
		if (debugging) {
			CIVLSource source = proc.getLocation().getSource();

			for (SymbolicExpression memUnit : memUnitPermissionMap.keySet()) {
				debugOut.print(symbolicAnalyzer.symbolicExpressionToString(
						source, state, memUnit));
				debugOut.print("(");
				if (memUnitPermissionMap.get(memUnit))
					debugOut.print("W");
				else
					debugOut.print("R");
				debugOut.print(")\t");
			}
			debugOut.println();
		}
		return memUnitPermissionMap;
	}

}
