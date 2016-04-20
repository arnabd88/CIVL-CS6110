package edu.udel.cis.vsl.civl.kripke;

import java.io.PrintStream;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import edu.udel.cis.vsl.civl.err.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.err.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.library.IF.LibraryEnabler;
import edu.udel.cis.vsl.civl.model.IF.SystemFunction;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.AssertStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.AssignStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.AssumeStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.MPIRecvStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.MPISendStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.MPIStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.MallocStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ReturnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.statement.WaitStatement;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.model.common.statement.StatementList;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.state.IF.DynamicScope;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.StackEntry;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.util.Pair;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * This class is responsible for computing the ample processes set at a given
 * state. It is a helper of Enabler. TODO: think about ways to realize the
 * independence between POR algorithm and system function implementations.
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

	/* **************************** Static Fields ************************** */

	/**
	 * The name of $comm_enqueu.
	 */
	private static final String COMM_ENQUE = "$comm_enqueue";

	/**
	 * The name of $comm_dequeu.
	 */
	private static final String COMM_DEQUE = "$comm_dequeue";

	/* *************************** Instance Fields ************************* */

	/**
	 * The map of active processes (i.e., non-null processes with non-empty
	 * stack that have at least one enabled statement) and the corresponding
	 * possible $comm_enqueue/$comm_dequeu function calls.
	 */
	Map<Integer, Set<CallOrSpawnStatement>> activeProcesses = new LinkedHashMap<>();

	/**
	 * Mapping of process ID's and the corresponding set of ample process ID's.
	 * Used for finding the smallest ample set.
	 */
	Map<Integer, Set<Integer>> ampleProcessesMap = new HashMap<>();

	/**
	 * The unique enabler used in the system. Used here for evaluating the guard
	 * of statements.
	 */
	private Enabler enabler;

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
	 * @param debug
	 *            The option to turn on/off the printing of debugging
	 *            information.
	 * @param debugOut
	 *            The print stream for debugging information.
	 */
	AmpleSetWorker(State state, Enabler enabler, Evaluator evaluator,
			boolean debug, PrintStream debugOut) {
		this.state = state;
		this.enabler = enabler;
		this.evaluator = evaluator;
		this.debugging = debug;
		this.debugOut = debugOut;
	}

	/* *********************** Package-private Methods ********************* */

	/**
	 * Obtain the set of ample processes for the current state.
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
			ampleProcessIDs = new LinkedHashSet<Integer>(
					activeProcesses.keySet());
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
		int minAmpleSetId = -1;// keep track of the smallest ample set

		preprocessing();
		for (int pid : activeProcesses.keySet()) {
			Set<Integer> ampleProcessIDs = ampleSetOfProcess(pid);

			ampleProcessesMap.put(pid, ampleProcessIDs);
			if (ampleProcessIDs.size() < minimalAmpleSetSize) {
				minAmpleSetId = pid;
				minimalAmpleSetSize = ampleProcessIDs.size();
			}
			if (minimalAmpleSetSize == 1)
				break;
		}
		for (int pid : ampleProcessesMap.get(minAmpleSetId)) {
			result.add(pid);
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
	private Set<Integer> ampleSetOfProcess(int startPid) {
		Set<Integer> ampleProcessIDs = new LinkedHashSet<>();
		Stack<Integer> workingProcessIDs = new Stack<>();

		workingProcessIDs.add(startPid);
		ampleProcessIDs.add(startPid);
		while (!workingProcessIDs.isEmpty()) {
			int pid = workingProcessIDs.pop();
			ProcessState thisProc = state.getProcessState(pid);
			Set<SymbolicExpression> impactMemUnits = impactMemUnitsMap.get(pid);
			Map<SymbolicExpression, Boolean> reachableMemUnitsMapOfThis = reachableMemUnitsMap
					.get(pid);
			Set<CallOrSpawnStatement> systemCalls = this.enabledSystemCallMap
					.get(pid);

			if (impactMemUnits == null) {
				// The current process is entering an atomic/atom block
				// whose impact memory units can't be computed
				// completely
				ampleProcessIDs = activeProcesses.keySet();
				return ampleProcessIDs;
			}
			if (systemCalls != null && !systemCalls.isEmpty()) {
				for (CallOrSpawnStatement call : systemCalls) {
					SystemFunction systemFunction = (SystemFunction) call
							.function();
					LibraryEnabler lib = enabler.libraryEnabler(
							call.getSource(), systemFunction.getLibrary());
					Set<Integer> ampleSubSet = lib.ampleSet(state, pid, call,
							reachableMemUnitsMap);

					if (ampleSubSet != null && !ampleSubSet.isEmpty()) {
						for (int amplePid : ampleSubSet) {
							if (amplePid != pid
									&& activeProcesses.keySet().contains(
											amplePid)
									&& !ampleProcessIDs.contains(amplePid)
									&& !workingProcessIDs.contains(amplePid)) {
								workingProcessIDs.add(amplePid);
								ampleProcessIDs.add(amplePid);
								if (ampleProcessIDs.size() == activeProcesses
										.keySet().size())
									return ampleProcessIDs;
							}
						}
					}
				}
			}
			for (Statement s : thisProc.getLocation().outgoing()) {
				// this process has a wait statement
				if (s instanceof WaitStatement) {
					int joinID = evaluator.joinedIDofWait(state, thisProc,
							(WaitStatement) s);

					if (!ampleProcessIDs.contains(joinID)
							&& workingProcessIDs.contains(joinID)) {
						workingProcessIDs.add(joinID);
						ampleProcessIDs.add(joinID);
						if (ampleProcessIDs.size() == activeProcesses.keySet()
								.size())
							break;
					}
				}
			}
			for (int otherPid : activeProcesses.keySet()) {
				Map<SymbolicExpression, Boolean> reachableMemUnitsMapOfOther;

				// add new ample id earlier
				if (otherPid == pid || ampleProcessIDs.contains(otherPid)
						|| workingProcessIDs.contains(otherPid))
					continue;
				reachableMemUnitsMapOfOther = reachableMemUnitsMap
						.get(otherPid);
				for (SymbolicExpression unit : impactMemUnits) {
					if (reachableMemUnitsMapOfOther.containsKey(unit)) {
						if ((reachableMemUnitsMapOfThis.get(unit) || reachableMemUnitsMapOfOther
								.get(unit))) {
							workingProcessIDs.add(otherPid);
							ampleProcessIDs.add(otherPid);
							break;
						}
					}
				}
				if (ampleProcessIDs.size() == activeProcesses.keySet().size())
					return ampleProcessIDs;
			}
		}
		return ampleProcessIDs;
	}

	/**
	 * Compute active processes at the current state, i.e., non-null processes
	 * with non-empty stack that have at least one enabled statements.
	 * 
	 */
	private void computeActiveProcesses() {
		for (ProcessState p : state.getProcessStates()) {
			boolean active = false;
			Set<CallOrSpawnStatement> commCalls;
			int pid;

			if (p == null || p.hasEmptyStack())
				continue;
			commCalls = new HashSet<>();
			pid = p.getPid();
			for (Statement s : p.getLocation().outgoing()) {
				if (!enabler.getGuard(s, pid, state).value.isFalse()) {
					active = true;
					if (s instanceof CallOrSpawnStatement) {
						CallOrSpawnStatement callOrSpawnStatement = (CallOrSpawnStatement) s;

						if (callOrSpawnStatement.isSystemCall()) {
							SystemFunction systemFunction = (SystemFunction) callOrSpawnStatement
									.function();
							String library = systemFunction.getLibrary();
							String name = systemFunction.name().name();

							if (library.equals("civlc")) {
								if (name.equals(COMM_DEQUE)
										|| name.equals(COMM_ENQUE)) {
									commCalls.add((CallOrSpawnStatement) s);
								}
							}
						}
					}
				}
			}
			if (active)
				activeProcesses.put(pid, commCalls);
		}
	}

	/**
	 * The impact memory units of a certain process at the current state. The
	 * computation could be incomplete when there is atomic/atom block that
	 * contains function calls.
	 * 
	 * @param p
	 *            The process whose impact memory units are to be computed.
	 * @return The impact memory units of the process and the status to denote
	 *         if the computation is complete.
	 */
	private Pair<MemoryUnitsStatus, Set<SymbolicExpression>> impactMemoryUnits(
			ProcessState p) {
		Set<SymbolicExpression> memUnits = new HashSet<>();
		int pid = p.getPid();
		Location pLocation = p.getLocation();
		Set<CallOrSpawnStatement> systemCalls = new HashSet<>();

		this.enabledSystemCallMap.put(pid, systemCalls);
		if (pLocation.enterAtom() || pLocation.enterAtomic()
				|| p.atomicCount() > 0) {
			return impactMemoryUnitsOfAtomicBlock(pLocation, pid);
		} else {
			for (Statement s : pLocation.outgoing()) {
				try {
					memUnits.addAll(impactMemoryUnitsOfStatement(s, pid));
				} catch (UnsatisfiablePathConditionException e) {
					continue;
				}
			}
		}
		return new Pair<>(MemoryUnitsStatus.NORMAL, memUnits);
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
								// assume that system functions are always ample
								// TODO check comm_deque and comm_enque for
								// hybrid mpi processes.
								if (!(callOrSpawnStatement.function() instanceof SystemFunction))
									return new Pair<MemoryUnitsStatus, Set<SymbolicExpression>>(
											MemoryUnitsStatus.INCOMPLETE,
											memUnits);
							}
						}
						try {
							memUnits.addAll(impactMemoryUnitsOfStatement(s, pid));
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
	private Set<SymbolicExpression> impactMemoryUnitsOfStatement(
			Statement statement, int pid)
			throws UnsatisfiablePathConditionException {
		Set<SymbolicExpression> memUnits = new HashSet<>();
		Set<SymbolicExpression> memUnitsPartial = memoryUnit(statement.guard(),
				pid);

		if (memUnitsPartial != null) {
			memUnits.addAll(memUnitsPartial);
		}
		switch (statement.statementKind()) {
		case ASSERT:
			AssertStatement assertStatement = (AssertStatement) statement;
			Expression assertExpression = assertStatement.getExpression();
			Expression[] printfArgs = assertStatement.printfArguments();

			memUnitsPartial = memoryUnit(assertExpression, pid);
			if (memUnitsPartial != null) {
				memUnits.addAll(memUnitsPartial);
			}
			if (printfArgs != null) {
				for (Expression argument : printfArgs) {
					memUnitsPartial = memoryUnit(argument, pid);
					if (memUnitsPartial != null) {
						memUnits.addAll(memUnitsPartial);
					}
				}
			}
			break;
		case ASSIGN:
		case CHOOSE:
			AssignStatement assignStatement = (AssignStatement) statement;

			memUnitsPartial = memoryUnit(assignStatement.getLhs(), pid);
			if (memUnitsPartial != null) {
				memUnits.addAll(memUnitsPartial);
			}
			memUnitsPartial = memoryUnit(assignStatement.rhs(), pid);
			if (memUnitsPartial != null) {
				memUnits.addAll(memUnitsPartial);
			}
			break;
		case ASSUME:
			AssumeStatement assumeStatement = (AssumeStatement) statement;
			Expression assumeExpression = assumeStatement.getExpression();

			memUnitsPartial = memoryUnit(assumeExpression, pid);
			if (memUnitsPartial != null) {
				memUnits.addAll(memUnitsPartial);
			}
			break;
		case CALL_OR_SPAWN:
			CallOrSpawnStatement call = (CallOrSpawnStatement) statement;

			if (call.isSystemCall()) {
				this.enabledSystemCallMap.get(pid).add(call);
			}
			for (Expression argument : call.arguments()) {
				memUnitsPartial = memoryUnit(argument, pid);
				if (memUnitsPartial != null) {
					memUnits.addAll(memUnitsPartial);
				}
			}
			break;
		case MALLOC:
			MallocStatement mallocStatement = (MallocStatement) statement;

			memUnitsPartial = memoryUnit(mallocStatement.getLHS(), pid);
			if (memUnitsPartial != null) {
				memUnits.addAll(memUnitsPartial);
			}
			memUnitsPartial = memoryUnit(mallocStatement.getScopeExpression(),
					pid);
			if (memUnitsPartial != null) {
				memUnits.addAll(memUnitsPartial);
			}
			memUnitsPartial = memoryUnit(mallocStatement.getSizeExpression(),
					pid);
			if (memUnitsPartial != null) {
				memUnits.addAll(memUnitsPartial);
			}
			break;
		case MPI:
			memUnitsPartial = impactMemoryUnitsOfMPIStatement(
					(MPIStatement) statement, pid);
			if (memUnitsPartial != null) {
				memUnits.addAll(memUnitsPartial);
			}
			break;
		case NOOP:
			break;
		case RETURN:
			ReturnStatement returnStatement = (ReturnStatement) statement;

			if (returnStatement.expression() != null) {
				memUnitsPartial = memoryUnit(returnStatement.expression(), pid);
				if (memUnitsPartial != null) {
					memUnits.addAll(memUnitsPartial);
				}
			}
			break;
		case STATEMENT_LIST:
			StatementList statementList = (StatementList) statement;

			for (Statement subStatement : statementList.statements()) {
				memUnits.addAll(impactMemoryUnitsOfStatement(subStatement, pid));
			}
			break;
		case WAIT:
			memUnitsPartial = memoryUnit(((WaitStatement) statement).process(),
					pid);
			if (memUnitsPartial != null) {
				memUnits.addAll(memUnitsPartial);
			}
			break;
		default:
			throw new CIVLUnimplementedFeatureException(
					"Impact memory units for statement: ", statement);
		}

		return memUnits;
	}

	/**
	 * Compute the impact memory units of an MPI statement.
	 * 
	 * @param statement
	 *            The MPI statement whose impact memory units are to be
	 *            computed.
	 * @param pid
	 *            The ID of the process that executes the MPI statement.
	 * @return the impact memory units of the given MPI statement
	 * @throws UnsatisfiablePathConditionException
	 */
	private Set<SymbolicExpression> impactMemoryUnitsOfMPIStatement(
			MPIStatement statement, int pid)
			throws UnsatisfiablePathConditionException {
		Set<SymbolicExpression> memUnits = new HashSet<>();
		Set<SymbolicExpression> memUnitsPartial;

		switch (statement.mpiStatementKind()) {
		case IBARRIER:
			break;
		case IRECV:
			break;
		case ISEND:
			break;
		case RECV:
			MPIRecvStatement mpiRecvStatement = (MPIRecvStatement) statement;

			for (Expression argument : mpiRecvStatement.getArgumentsList()) {
				memUnitsPartial = memoryUnit(argument, pid);
				if (memUnitsPartial != null) {
					memUnits.addAll(memUnitsPartial);
				}
			}
			break;
		case SEND:
			// TODO: why the program never goes there ?
			MPISendStatement mpiSendStatement = (MPISendStatement) statement;

			for (Expression argument : mpiSendStatement.getArgumentsList()) {
				memUnitsPartial = memoryUnit(argument, pid);
				if (memUnitsPartial != null) {
					memUnits.addAll(memUnitsPartial);
				}
			}
			break;
		case WAIT:
			break;
		default:
			throw new CIVLUnimplementedFeatureException(
					"Impact memory units for statement: ", statement);
		}
		return memUnits;
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
	private Set<SymbolicExpression> memoryUnit(Expression expression, int pid)
			throws UnsatisfiablePathConditionException {
		Set<SymbolicExpression> memoryUnits = new HashSet<>();

		evaluator.memoryUnitsOfExpression(state, pid, expression, memoryUnits);
		if (debugging) {
			printMemoryUnitsOfExpression(expression, memoryUnits);
		}
		// printMemoryUnitsOfExpression(expression, memoryUnits);
		return memoryUnits;
	}

	/**
	 * Pre-processing for ample set computation, including:
	 * <ul>
	 * <li>Compute the impact memory units for each process; and</li>
	 * <li>Compute the reachable memory units for each process.</li>
	 * </ul>
	 */
	private void preprocessing() {
		for (int pid : activeProcesses.keySet()) {
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
	 * Print the impact memory units of a expression. Used for debugging.
	 * 
	 * @param expression
	 *            The expression to be printed.
	 * @param memUnits
	 *            The memory units of the expression.
	 */
	private void printMemoryUnitsOfExpression(Expression expression,
			Set<SymbolicExpression> memUnits) {
		debugOut.println(expression.toString() + "\t mem units:");
		for (SymbolicExpression memUnit : memUnits) {
			debugOut.print(memUnit + "\t");
		}
		debugOut.println();
	}

	/**
	 * Given a process, compute the set of reachable memory units and if the
	 * memory unit could be modified at the current location or any future
	 * location.
	 * 
	 * @param p
	 *            The process whose reachable memory units are to be computed.
	 * @return A map of reachable memory units and if they could be modified by
	 *         the process.
	 */
	private Map<SymbolicExpression, Boolean> reachableMemoryUnits(ProcessState p) {
		Set<Integer> checkedDyScopes = new HashSet<>();
		Map<SymbolicExpression, Boolean> memUnitPermissionMap = new HashMap<>();
		Set<Variable> writableVariables = p.getLocation().writableVariables();
		// only look at the top stack is sufficient
		StackEntry callStack = p.peekStack();
		int dyScopeID = callStack.scope();

		while (dyScopeID >= 0) {
			if (checkedDyScopes.contains(dyScopeID))
				break;
			else {
				DynamicScope dyScope = state.getScope(dyScopeID);
				int size = dyScope.numberOfValues();

				for (int vid = 0; vid < size; vid++) {
					Variable variable = dyScope.lexicalScope().variable(vid);
					Set<SymbolicExpression> varMemUnits = evaluator
							.memoryUnitsOfVariable(dyScope.getValue(vid),
									dyScopeID, vid, state);
					boolean permission = writableVariables.contains(variable) ? true
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
		return memUnitPermissionMap;
	}

}
