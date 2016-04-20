/**
 * 
 */
package edu.udel.cis.vsl.civl.semantics.common;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.civl.analysis.IF.Analysis;
import edu.udel.cis.vsl.civl.analysis.IF.CodeAnalyzer;
import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.config.IF.CIVLConstants;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.mpi.LibmpiExecutor;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.log.IF.CIVLExecutionException;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.Certainty;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLSyntaxException;
import edu.udel.cis.vsl.civl.model.IF.CIVLTypeFactory;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.SystemFunction;
import edu.udel.cis.vsl.civl.model.IF.expression.ContractClauseExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DotExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.AssignStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.AtomicLockAssignStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.CivlForEnterStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.CivlParForSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.MallocStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.NoopStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ReturnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement.StatementKind;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPointerType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLStructOrUnionType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.model.common.FunctionTranslator;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.Format;
import edu.udel.cis.vsl.civl.semantics.IF.Format.ConversionType;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryLoaderException;
import edu.udel.cis.vsl.civl.semantics.IF.NoopTransition;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.semantics.IF.Transition;
import edu.udel.cis.vsl.civl.semantics.IF.Transition.AtomicLockAction;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.StackEntry;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.civl.util.IF.Triple;
import edu.udel.cis.vsl.gmc.ErrorLog;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SARLException;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicUnionType;

/**
 * An executor is used to execute a CIVL statement. The basic method provided
 * takes a state and a statement, and modifies the state according to the
 * semantics of that statement.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonExecutor implements Executor {

	/* *************************** Instance Fields ************************* */

	/** The Evaluator used to evaluate expressions. */
	private Evaluator evaluator;

	/**
	 * The loader used to find Executors for system functions declared in
	 * libraries.
	 */
	private LibraryExecutorLoader loader;

	/**
	 * The unique model factory used in the system.
	 */
	private ModelFactory modelFactory;

	/**
	 * The unique model factory used in the system.
	 */
	private CIVLTypeFactory typeFactory;

	/**
	 * The number of steps that have been executed by this executor. A "step" is
	 * defined to be a call to method
	 * {@link #executeWork(State, int, Statement)}.
	 */
	private long numSteps = 0;

	/** The factory used to produce and manipulate model states. */
	private StateFactory stateFactory;

	private SymbolicUtility symbolicUtil;

	/** The symbolic universe used to manage all symbolic expressions. */
	private SymbolicUniverse universe;

	private CIVLErrorLogger errorLogger;

	private CIVLConfiguration civlConfig;

	private SymbolicAnalyzer symbolicAnalyzer;

	private IntObject zeroObj;

	private IntObject oneObj;

	private IntObject twoObj;

	/**
	 * The set of characters that are used to construct a number in a format
	 * string.
	 */
	private Set<Character> numbers;

	private List<CodeAnalyzer> analyzers;

	/* ***************************** Constructors ************************** */

	/**
	 * Create a new instance of executor.
	 * 
	 * @param modelFactory
	 *            The model factory of the system.
	 * @param stateFactory
	 *            The state factory of the system.
	 * @param log
	 *            The error logger of the system.
	 * @param loader
	 *            The library executor loader for executing system functions.
	 * @param evaluator
	 *            The CIVL evaluator for evaluating expressions.
	 * @param symbolicAnalyzer
	 *            The symbolic analyzer used in the system.
	 * @param errorLogger
	 *            The error logger to log errors
	 * @param civlConfig
	 *            The CIVL configuration.
	 */
	public CommonExecutor(ModelFactory modelFactory, StateFactory stateFactory,
			ErrorLog log, LibraryExecutorLoader loader, Evaluator evaluator,
			SymbolicAnalyzer symbolicAnalyzer, CIVLErrorLogger errorLogger,
			CIVLConfiguration civlConfig) {
		this.civlConfig = civlConfig;
		this.universe = modelFactory.universe();
		this.stateFactory = stateFactory;
		this.modelFactory = modelFactory;
		this.typeFactory = modelFactory.typeFactory();
		this.evaluator = evaluator;
		this.symbolicAnalyzer = symbolicAnalyzer;
		this.loader = loader;
		this.symbolicUtil = evaluator.symbolicUtility();
		this.errorLogger = errorLogger;
		this.zeroObj = universe.intObject(0);
		this.oneObj = universe.intObject(1);
		this.twoObj = universe.intObject(2);
		numbers = new HashSet<Character>(10);
		for (int i = 0; i < 10; i++) {
			numbers.add(Character.forDigit(i, 10));
		}
		this.analyzers = modelFactory.codeAnalyzers();
	}

	/* ************************** Private methods ************************** */

	/**
	 * Executes an assignment statement. The state will be updated such that the
	 * value of the left-hand-side of the assignment statement is the result of
	 * evaluating the right-hand-side. The location of the state will be updated
	 * to the target location of the assignment.
	 * 
	 * @param state
	 *            The state of the program
	 * @param pid
	 *            The process id of the currently executing process
	 * @param statement
	 *            An assignment statement to be executed
	 * @return The updated state of the program
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeAssign(State state, int pid, String process,
			AssignStatement statement)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluator.evaluate(state, pid, statement.rhs());

		if (statement instanceof AtomicLockAssignStatement) {
			AtomicLockAssignStatement atomicLockAssign = (AtomicLockAssignStatement) statement;
			ProcessState procState = state.getProcessState(pid), newProcState;
			int atomicCount = procState.atomicCount();

			if (atomicLockAssign.enterAtomic()) {
				newProcState = procState.incrementAtomicCount();
				if (atomicCount == 0)
					state = stateFactory.getAtomicLock(state, pid);
			} else {// leave atomic
				newProcState = procState.decrementAtomicCount();
				if (atomicCount == 1)
					state = stateFactory.releaseAtomicLock(state);
			}
			state = stateFactory.setProcessState(state, newProcState);
		} else
			state = assign(eval.state, pid, process, statement.getLhs(),
					eval.value, statement.isInitialization());

		state = stateFactory.setLocation(state, pid, statement.target(), true);
		return state;
	}

	/**
	 * Executes a call statement. The state will be updated such that the
	 * process is at the start location of the function, a new dynamic scope for
	 * the function is created, and function parameters in the new scope have
	 * the values that are passed as arguments.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The process id of the currently executing process.
	 * @param statement
	 *            A call statement to be executed.
	 * @return The updated state of the program.
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeCall(State state, int pid,
			CallOrSpawnStatement statement)
			throws UnsatisfiablePathConditionException {
		if (statement.function() instanceof SystemFunction) {
			state = this.executeSystemFunctionCall(state, pid, statement,
					(SystemFunction) statement.function());
		} else {
			CIVLFunction function = statement.function();
			SymbolicExpression[] arguments;

			arguments = new SymbolicExpression[statement.arguments().size()];
			for (int i = 0; i < statement.arguments().size(); i++) {
				Evaluation eval = evaluator.evaluate(state, pid, statement
						.arguments().get(i));

				state = eval.state;
				arguments[i] = eval.value;
			}
			Analysis.analyzeCall(this.analyzers, state, pid, statement,
					arguments);
			if (function == null) {
				Triple<State, CIVLFunction, Integer> eval = evaluator
						.evaluateFunctionIdentifier(state, pid,
								statement.functionExpression(),
								statement.getSource());

				function = eval.second;
				state = eval.first;
				if (function.isRootFunction()) {
					state = this.executeSystemFunctionCall(state, pid,
							statement, (SystemFunction) function);
				} else
					state = stateFactory.pushCallStack(state, pid, function,
							eval.third, arguments);
			} else
				state = stateFactory.pushCallStack(state, pid, function,
						arguments);
		}
		// Right after the call stack entry is pushed into call stack, check
		// pre-conditions:
		if (civlConfig.isEnableMpiContract()) {
			List<ContractClauseExpression> preconditions = statement.function()
					.preconditions();

			if (preconditions != null && !preconditions.isEmpty())
				this.assertMPIContractClauses(state, pid, preconditions);
		}
		return state;
	}

	private State executeSystemFunctionCall(State state, int pid,
			CallOrSpawnStatement call, SystemFunction function)
			throws UnsatisfiablePathConditionException {
		String libraryName = function.getLibrary();
		String funcName = function.name().name();

		try {
			LibraryExecutor executor = loader.getLibraryExecutor(libraryName,
					this, this.modelFactory, this.symbolicUtil,
					symbolicAnalyzer);

			state = executor.execute(state, pid, call, funcName);
		} catch (LibraryLoaderException exception) {
			String process = state.getProcessState(pid).name() + "(id=" + pid
					+ ")";

			errorLogger.logSimpleError(call.getSource(), state, process,
					symbolicAnalyzer.stateInformation(state),
					ErrorKind.LIBRARY,
					"unable to load the library executor for the library "
							+ libraryName + " to execute the function "
							+ funcName);
			if (call.lhs() != null)
				state = this.assign(state, pid, process, call.lhs(),
						universe.nullExpression());
			state = this.stateFactory.setLocation(state, pid, call.target());
		}
		return state;
	}

	/**
	 * execute malloc statement. TODO complete javadocs
	 * 
	 * @param state
	 * @param pid
	 * @param statement
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeMalloc(State state, int pid, String process,
			MallocStatement statement)
			throws UnsatisfiablePathConditionException {
		CIVLSource source = statement.getSource();
		LHSExpression lhs = statement.getLHS();
		Evaluation eval;
		SymbolicExpression scopeValue;
		int dyScopeID;
		NumericExpression mallocSize, elementSize;
		BooleanExpression pathCondition, claim;
		ResultType validity;
		NumericExpression elementCount;
		Pair<State, SymbolicExpression> mallocResult;
		SymbolicType dynamicElementType;

		eval = evaluator.evaluate(state, pid, statement.getScopeExpression());
		state = eval.state;
		scopeValue = eval.value;
		dyScopeID = modelFactory.getScopeId(statement.getScopeExpression()
				.getSource(), scopeValue);
		eval = evaluator.evaluate(state, pid, statement.getSizeExpression());
		state = eval.state;
		mallocSize = (NumericExpression) eval.value;
		eval = evaluator.evaluateSizeofType(source, state, pid,
				statement.getStaticElementType());
		state = eval.state;
		elementSize = (NumericExpression) eval.value;
		pathCondition = state.getPathCondition();
		claim = universe.divides(elementSize, mallocSize);
		validity = universe.reasoner(pathCondition).valid(claim)
				.getResultType();
		if (validity != ResultType.YES) {
			String elementType = statement.getStaticElementType().toString();
			String message = "For a $malloc returning " + elementType
					+ "*, the size argument must be a multiple of sizeof("
					+ elementType + ")\n" + "      actual size argument: "
					+ mallocSize.toString() + "\n"
					+ "      expected size argument: a multile of "
					+ elementSize.toString();

			state = errorLogger.logError(source, state, process,
					symbolicAnalyzer.stateInformation(state), claim, validity,
					ErrorKind.MALLOC, message);
			// state = state.setPathCondition(universe.and(pathCondition,
			// claim));
			throw new UnsatisfiablePathConditionException();
		}
		elementCount = universe.divide(mallocSize, elementSize);
		// If the type of the allocated element object is an struct or union
		// type, field types can be array types which should be evaluated
		// carefully to provide extents informations.
		if (statement.getStaticElementType().isStructType()) {
			CIVLStructOrUnionType staticType = (CIVLStructOrUnionType) statement
					.getStaticElementType();
			int numFields = staticType.numFields();
			SymbolicType fieldTypes[] = new SymbolicType[numFields];

			for (int i = 0; i < numFields; i++) {
				CIVLType civlfieldType = (CIVLType) staticType.getField(i)
						.type();

				if (civlfieldType.isArrayType()) {
					Pair<State, SymbolicArrayType> pair = evaluator
							.evaluateCIVLArrayType(state, pid,
									(CIVLArrayType) civlfieldType);

					state = pair.left;
					fieldTypes[i] = pair.right;
				} else
					fieldTypes[i] = civlfieldType.getDynamicType(universe);
			}
			dynamicElementType = universe.tupleType(
					universe.stringObject(staticType.name().name()),
					Arrays.asList(fieldTypes));
		} else
			dynamicElementType = statement.getDynamicElementType();
		mallocResult = stateFactory.malloc(state, pid, dyScopeID,
				statement.getMallocId(), dynamicElementType, elementCount);
		state = mallocResult.left;
		if (lhs != null)
			state = assign(state, pid, process, lhs, mallocResult.right);
		state = stateFactory.setLocation(state, pid, statement.target(),
				lhs != null);
		return state;
	}

	/**
	 * Execute a return statement.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The process id of the currently executing process.
	 * @param statement
	 *            The return statement to be executed.
	 * @return The updated state of the program.
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeReturn(State state, int pid, String process,
			ReturnStatement statement)
			throws UnsatisfiablePathConditionException {
		Expression expr = statement.expression();
		ProcessState processState;
		SymbolicExpression returnValue;
		CIVLFunction function;
		String functionName;

		processState = state.getProcessState(pid);
		function = processState.peekStack().location().function();
		functionName = function.name().name();
		if (functionName.equals(CIVLConstants.civlSystemFunction)) {
			assert pid == 0;
			if (state.numProcs() > 1) {
				for (ProcessState proc : state.getProcessStates()) {
					if (proc == null)
						continue;
					if (proc.getPid() == pid)
						continue;
					if (!this.civlConfig.svcomp() && !proc.hasEmptyStack()) {
						errorLogger
								.logSimpleError(statement.getSource(), state,
										process, symbolicAnalyzer
												.stateInformation(state),
										ErrorKind.PROCESS_LEAK,
										"attempt to terminate the main process while process "
												+ proc.identifier()
												+ "(process<" + proc.getPid()
												+ ">) is still running");
					}
				}
			}

		}
		if (expr == null)
			returnValue = null;
		else {
			Evaluation eval = evaluator.evaluate(state, pid, expr);

			returnValue = eval.value;
			state = eval.state;
			if (functionName.equals("_CIVL_system")) {
				if (universe.equals(returnValue, universe.integer(0)).isFalse()) {
					this.errorLogger.logSimpleError(statement.getSource(),
							state, process,
							symbolicAnalyzer.stateInformation(state),
							ErrorKind.OTHER, "program exits with error code: "
									+ returnValue);
				}
			}
		}
		// Before popping call stack, check post-conditions if -mpiContract
		// option is selected.
		if (civlConfig.isEnableMpiContract()) {
			List<ContractClauseExpression> postconditions = function
					.postconditions();

			if (postconditions != null && !postconditions.isEmpty()) {
				Scope outerScope = function.outerScope();
				Variable resultVar = outerScope
						.variable(FunctionTranslator.contractResultName);

				// replacing $result if it exists:
				if (resultVar != null) {
					int sid = state.getDyscope(pid, outerScope);

					if (returnValue != null) {
						state = stateFactory.setVariable(state,
								resultVar.vid(), sid, returnValue);
						state = assertMPIContractClauses(state, pid,
								postconditions);
					} else {
						CIVLSource ensuresSource = postconditions.get(0)
								.getSource();

						errorLogger.logSimpleError(ensuresSource, state,
								process, symbolicAnalyzer.stateToString(state),
								ErrorKind.OTHER, "Function: " + functionName
										+ "has no return value but the "
										+ "contracts of it uses $result");
						// If there is no return value but $result is used in
						// contract, ignore all contracts.
					}
				} else
					state = assertMPIContractClauses(state, pid, postconditions);
			}
		}
		state = stateFactory.popCallStack(state, pid);
		processState = state.getProcessState(pid);
		if (!processState.hasEmptyStack()) {
			StackEntry returnContext = processState.peekStack();
			Location returnLocation = returnContext.location();
			CallOrSpawnStatement call = (CallOrSpawnStatement) returnLocation
					.getSoleOutgoing();

			if (call.lhs() != null) {
				if (returnValue == null) {
					errorLogger.logSimpleError(call.getSource(), state,
							process, symbolicAnalyzer.stateInformation(state),
							ErrorKind.OTHER,
							"attempt to use the return value of function "
									+ functionName + " when " + functionName
									+ " has returned without a return value.");
					returnValue = universe.nullExpression();
				}
				state = assign(state, pid, process, call.lhs(), returnValue);
			}
			state = stateFactory.setLocation(state, pid, call.target(),
					call.lhs() != null);
		}
		return state;
	}

	/**
	 * Evaluates a list of contract clauses, once a contract clause being
	 * evaluated as unsatisfiable, an error will be reported.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param conditions
	 *            The List of contract clauses
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State assertMPIContractClauses(State state, int pid,
			List<ContractClauseExpression> conditions)
			throws UnsatisfiablePathConditionException {
		LibmpiExecutor libexec = null;
		String process = state.getProcessState(pid).name() + "(id=" + pid + ")";

		for (ContractClauseExpression condition : conditions) {
			Expression clauseBody = condition.getBody();

			if (condition.isCollectiveClause()) {
				// if the contract is a collective contract, loads library
				// evaluator
				Expression group = condition.getCollectiveGroup();
				Expression[] args = { group, clauseBody };

				if (libexec == null)
					try {
						libexec = (LibmpiExecutor) loader.getLibraryExecutor(
								"mpi", this, modelFactory, symbolicUtil,
								symbolicAnalyzer);
					} catch (LibraryLoaderException e) {
						errorLogger.logSimpleError(condition.getSource(),
								state, process,
								symbolicAnalyzer.stateInformation(state),
								ErrorKind.LIBRARY,
								"unable to load the library executor for the library "
										+ "mpi" + " to check mpi contracts");
						break;
					}
				state = libexec.executeCollectiveContract(state, pid, process,
						args, condition.contractKind(), condition.getSource());
			} else {
				Expression conditionExpr = condition.getBody();
				Reasoner reasoner = universe.reasoner(state.getPathCondition());
				Evaluation eval = evaluator.evaluate(state, pid, conditionExpr);
				ResultType resultType = reasoner.valid(
						(BooleanExpression) eval.value).getResultType();

				state = eval.state;
				// Check non-collective conditions once
				if (!resultType.equals(ResultType.YES))
					state = reportContractViolation(state,
							conditionExpr.getSource(), pid, resultType,
							(BooleanExpression) eval.value, conditionExpr,
							ErrorKind.CONTRACT, null);
			}
		}
		return state;
	}

	/**
	 * Executes a spawn statement. The state will be updated with a new process
	 * whose start location is the beginning of the forked function.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The process id of the currently executing process.
	 * @param statement
	 *            A spawn statement to be executed.
	 * @return The updated state of the program.
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeSpawn(State state, int pid, String process,
			CallOrSpawnStatement statement)
			throws UnsatisfiablePathConditionException {
		CIVLFunction function = statement.function();
		int newPid = state.numProcs();
		List<Expression> argumentExpressions = statement.arguments();
		int numArgs = argumentExpressions.size();
		SymbolicExpression[] arguments = new SymbolicExpression[numArgs];
		int parentDyscopeId = -1;

		assert !statement.isCall();
		if (function == null) {
			Triple<State, CIVLFunction, Integer> eval = evaluator
					.evaluateFunctionIdentifier(state, pid,
							statement.functionExpression(),
							statement.getSource());

			state = eval.first;
			function = eval.second;
			parentDyscopeId = eval.third;
		}
		for (int i = 0; i < numArgs; i++) {
			CIVLType expectedType = function.parameters().get(i).type();
			Evaluation eval;
			Expression actualArg = argumentExpressions.get(i);

			if (!actualArg.getExpressionType().equals(expectedType))
				eval = evaluator.evaluateCastWorker(state, pid, process,
						expectedType, actualArg);
			else
				eval = evaluator.evaluate(state, pid,
						argumentExpressions.get(i));
			state = eval.state;
			arguments[i] = eval.value;
		}
		if (parentDyscopeId >= 0)

			state = stateFactory.addProcess(state, function, parentDyscopeId,
					arguments, pid);
		else
			state = stateFactory.addProcess(state, function, arguments, pid);
		if (statement.lhs() != null)
			state = assign(state, pid, process, statement.lhs(),
					modelFactory.processValue(newPid));
		state = stateFactory.setLocation(state, pid, statement.target(),
				statement.lhs() != null);
		// state = stateFactory.computeReachableMemUnits(state, newPid);
		return state;
	}

	/**
	 * Returns the state that results from executing the statement, or null if
	 * path condition becomes unsatisfiable.
	 * 
	 * @param state
	 * @param pid
	 * @param statement
	 * @return
	 */
	private State executeStatement(State state, int pid, Statement statement)
			throws UnsatisfiablePathConditionException {
		try {
			statement.reached();
			return executeWork(state, pid, statement);
			// return this.stateFactory.simplify(state);
		} catch (SARLException e) {
			// e.printStackTrace(System.err);
			// System.err.flush();
			throw new CIVLInternalException("SARL exception: " + e, statement);
		} // catch (CIVLExecutionException e) {
			// errorLogger.reportError(e);
			// throw new UnsatisfiablePathConditionException();
			// }
	}

	/**
	 * Execute a generic statement. All statements except a Choose should be
	 * handled by this method.
	 * 
	 * @param State
	 *            The state of the program.
	 * @param pid
	 *            The process id of the currently executing process.
	 * @param statement
	 *            The statement to be executed.
	 * @return The updated state of the program.
	 */
	private State executeWork(State state, int pid, Statement statement)
			throws UnsatisfiablePathConditionException {
		int processIdentifier = state.getProcessState(pid).identifier();
		String process = "p" + processIdentifier + " (id = " + pid + ")";
		StatementKind kind = statement.statementKind();

		numSteps++;
		switch (kind) {
		case ASSIGN:
			return executeAssign(state, pid, process,
					(AssignStatement) statement);
			// case ASSUME:
			// return executeAssume(state, pid, (AssumeStatement) statement);
			// case ASSERT:
			// return executeAssert(state, pid, (AssertStatement) statement);
		case CALL_OR_SPAWN:
			CallOrSpawnStatement call = (CallOrSpawnStatement) statement;

			if (call.isCall())
				return executeCall(state, pid, call);
			else
				return executeSpawn(state, pid, process, call);
		case MALLOC:
			return executeMalloc(state, pid, process,
					(MallocStatement) statement);
		case NOOP: {
			Expression expression = ((NoopStatement) statement).expression();

			if (expression != null) {
				Evaluation eval = this.evaluator.evaluate(state, pid,
						expression);

				state = eval.state;
			}
			return stateFactory.setLocation(state, pid, statement.target());
		}
		case RETURN:
			return executeReturn(state, pid, process,
					(ReturnStatement) statement);
		case CIVL_FOR_ENTER:
			return executeNextInDomain(state, pid,
					(CivlForEnterStatement) statement);
		case CIVL_PAR_FOR_ENTER:
			return executeCivlParFor(state, pid,
					(CivlParForSpawnStatement) statement);
		default:
			throw new CIVLInternalException("Unknown statement kind: " + kind,
					statement);
		}
	}

	// private State executeAssert(State state, int pid, AssertStatement
	// assertStmt)
	// throws UnsatisfiablePathConditionException {
	// BooleanExpression assertValue;
	// Evaluation eval;
	// Reasoner reasoner;
	// ValidityResult valid;
	// ResultType resultType;
	// CIVLSource source = assertStmt.getSource();
	// String process = state.getProcessState(pid).name() + "(id=" + pid + ")";
	//
	// eval = evaluator.evaluate(state, pid, assertStmt.getCondition());
	// assertValue = (BooleanExpression) eval.value;
	// state = eval.state;
	// reasoner = universe.reasoner(state.getPathCondition());
	// valid = reasoner.valid(assertValue);
	// resultType = valid.getResultType();
	// if (resultType != ResultType.YES) {
	// Expression[] explanation = assertStmt.getExplanation();
	//
	// if (explanation != null) {
	// // if (civlConfig.enablePrintf()) {
	// SymbolicExpression[] pArgumentValues = new
	// SymbolicExpression[explanation.length];
	//
	// for (int i = 0; i < explanation.length; i++) {
	// eval = this.evaluator.evaluate(state, pid, explanation[i]);
	// state = eval.state;
	// pArgumentValues[i] = eval.value;
	// }
	// state = this.execute_printf(source, state, pid, process, null,
	// explanation, pArgumentValues, true);
	// civlConfig.out().println();
	// // }
	// }
	//
	// // if (arguments.length > 1) {
	// // if (civlConfig.enablePrintf()) {
	// // Expression[] pArguments = Arrays.copyOfRange(arguments, 1,
	// // arguments.length);
	// // SymbolicExpression[] pArgumentValues = Arrays.copyOfRange(
	// // argumentValues, 1, argumentValues.length);
	// //
	// // state = this.execute_printf(source, state, pid, process,
	// // null, pArguments, pArgumentValues);
	// // }
	// // }
	// state = errorLogger.logError(source, state, process,
	// symbolicAnalyzer.stateToString(state), assertValue,
	// resultType, ErrorKind.ASSERTION_VIOLATION,
	// "Cannot prove assertion holds: " + assertStmt.toString()
	// + "\n  Path condition: " + state.getPathCondition()
	// + "\n  Assertion: " + assertValue + "\n");
	// }
	// state = stateFactory.setLocation(state, pid, assertStmt.target());
	// return state;
	// }

	/**
	 * When the domain is empty, this is equivalent to a noop.
	 * 
	 * @param state
	 * @param pid
	 * @param parFor
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeCivlParFor(State state, int pid,
			CivlParForSpawnStatement parFor)
			throws UnsatisfiablePathConditionException {
		CIVLSource source = parFor.getSource();
		Expression domain = parFor.domain();
		VariableExpression domSize = parFor.domSizeVar();
		Evaluation eval;
		SymbolicExpression domainValue;
		// TODO why initializes domSizeValue with 1?
		NumericExpression domSizeValue;
		// TODO: why is dim -1 sometimes?
		int dim = parFor.dimension();
		String process = state.getProcessState(pid).name() + "(id=" + pid + ")";
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		IntegerNumber number_domSize;
		VariableExpression parProcsVar = parFor.parProcsVar();

		state = this.stateFactory.simplify(state);
		eval = evaluator.evaluate(state, pid, domain);
		domainValue = eval.value;
		state = eval.state;
		domSizeValue = symbolicUtil.getDomainSize(domainValue);
		state = this.assign(state, pid, process, domSize, domSizeValue);
		number_domSize = (IntegerNumber) reasoner.extractNumber(domSizeValue);
		if (number_domSize == null) {
			this.errorLogger.logSimpleError(source, state, process,
					symbolicAnalyzer.stateToString(state), ErrorKind.OTHER,
					"The arguments of the domain for $parfor "
							+ "must be concrete.");
			// throw new UnsatisfiablePathConditionException();
		} else if (!number_domSize.isZero()) {
			// only spawns processes when the domain is not empty.
			// InitialValueExpression initVal = modelFactory
			// .initialValueExpression(parProcs.getSource(),
			// parProcsVar.variable());
			// eval = evaluator.evaluate(state, pid, initVal);
			// state = eval.state;
			// state = this.assign(state, pid, process, parProcsVar,
			// eval.value);
			state = this.executeSpawns(state, pid, parProcsVar,
					parFor.parProcFunction(), dim, domainValue);
		}
		state = stateFactory.setLocation(state, pid, parFor.target(), true);
		return state;
	}

	/**
	 * Spawns new processes as a part of the execution of $parfor. For EVERY
	 * ELEMENT in domain, it will spawn a process to execute it.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param parProcs
	 *            The expression of the pointer to the first element of
	 *            processes array.
	 * @param parProcsPointer
	 *            The symbolic expression of the pointer to the first element of
	 *            processes array.
	 * @param function
	 *            The function will be spawned
	 * @param dim
	 *            The dimension number of the domain.
	 * @param domainValue
	 *            The symbolic expression of the domain object.
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeSpawns(State state, int pid,
			VariableExpression parProcsVar, CIVLFunction function, int dim,
			SymbolicExpression domainValue)
			throws UnsatisfiablePathConditionException {
		String process = state.getProcessState(pid).name() + "(id=" + pid + ")";
		List<SymbolicExpression> myValues = null;
		// int procPtrOffset = 0;
		// CIVLSource source = parProcs.getSource();
		Iterator<List<SymbolicExpression>> domainIter;
		List<SymbolicExpression> processes = new ArrayList<>();

		// Here we assume this operation contains all iterations in the domain.
		// All iterations means that it iterates from the least element to the
		// greatest element in the given domain.
		domainIter = symbolicUtil.getDomainIterator(domainValue);
		while (domainIter.hasNext()) {
			SymbolicExpression[] arguments = new SymbolicExpression[dim];
			// SymbolicExpression procPointer;
			// Evaluation eval;
			int newPid;

			myValues = domainIter.next();
			myValues.toArray(arguments);
			newPid = state.numProcs();
			state = stateFactory.addProcess(state, function, arguments, pid);
			// state = stateFactory.computeReachableMemUnits(state, newPid);
			// eval = evaluator.evaluatePointerAdd(state, process,
			// parProcsPointer, universe.integer(procPtrOffset++), false,
			// source).left; // no need for checking output
			// procPointer = eval.value;
			// state = eval.state;
			processes.add(modelFactory.processValue(newPid));
			// state = this.assign(source, state, process, procPointer,
			// modelFactory.processValue(newPid));
		}
		state = this.assign(state, pid, process, parProcsVar, universe.array(
				this.modelFactory.typeFactory().processSymbolicType(),
				processes));
		return state;
	}

	/**
	 * Giving a domain and a element of the domain, returns the subsequence of
	 * the element in domain. <br>
	 * Pre-condition: it's guaranteed by a nextInDomain condition checking sthat
	 * the element has a subsequence in the domain.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param nextInDomain
	 *            The nextInDomain statement.
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeNextInDomain(State state, int pid,
			CivlForEnterStatement nextInDomain)
			throws UnsatisfiablePathConditionException {
		List<Variable> loopVars = nextInDomain.loopVariables();
		Expression domain = nextInDomain.domain();
		CIVLSource source = nextInDomain.getSource();
		SymbolicExpression domValue;
		Evaluation eval = evaluator.evaluate(state, pid, domain);
		int dim = loopVars.size();
		String process = state.getProcessState(pid).name() + "(id=" + pid + ")";
		List<SymbolicExpression> varValues = new LinkedList<>();
		List<SymbolicExpression> nextEleValues = new LinkedList<>();
		boolean isAllNull = true;

		domValue = eval.value;
		state = eval.state;
		// Evaluates the element given by the statement
		for (int i = 0; i < dim; i++) {
			SymbolicExpression varValue = state.valueOf(pid, loopVars.get(i));

			if (!varValue.isNull())
				isAllNull = false;
			varValues.add(varValue);
		}
		// Check if it's literal domain or rectangular domain
		try {
			if (symbolicUtil.isLiteralDomain(domValue)) {
				SymbolicExpression literalDomain;
				SymbolicExpression nextElement = null;
				SymbolicExpression counterValue;
				int counter = -1; // The concrete literal counter value
				Variable literalCounterVar;

				literalDomain = universe.unionExtract(oneObj,
						universe.tupleRead(domValue, twoObj));
				literalCounterVar = nextInDomain.getLiteralDomCounter();
				counterValue = state.valueOf(pid, literalCounterVar);
				// Evaluate the value of the counter variable. Here we can
				// initialize it as 0 or search the specific value from the
				// given domain element if the variable is uninitialized.If it
				// does initialization already, read the value from this
				// variable.
				// TODO why counterValue can be null (not SARL NULL)?
				if (counterValue.isNull() || counterValue == null) {
					// If the counter is not initialized
					if (isAllNull)// this is the first iteration
						counter = 0;
					else
						counter = symbolicUtil.literalDomainSearcher(
								literalDomain, varValues, dim);
				} else
					counter = ((IntegerNumber) universe
							.extractNumber((NumericExpression) counterValue))
							.intValue();

				if (counter == -1)
					throw new CIVLExecutionException(ErrorKind.OTHER,
							Certainty.CONCRETE, process,
							"Loop variables are not belong to the domain",
							this.symbolicAnalyzer.stateInformation(state),
							source);
				// it's guaranteed that this iteration will have a
				// subsequence.
				if (counter < ((IntegerNumber) universe
						.extractNumber((NumericExpression) universe
								.length(literalDomain))).intValue())
					nextElement = universe.arrayRead(literalDomain,
							universe.integer(counter));
				else
					throw new CIVLInternalException(
							"Domain iteration out of bound", source);
				// increase the counter
				counter++;
				state = stateFactory.setVariable(state, literalCounterVar, pid,
						universe.integer(counter));
				// Put domain element into a list
				for (int i = 0; i < dim; i++)
					nextEleValues.add(universe.arrayRead(nextElement,
							universe.integer(i)));
				// This function is guaranteed have a next element, so it doesnt
				// need to consider the loop end situation
			} else if (symbolicUtil.isRectangularDomain(domValue)) {
				// If it's rectangular domain, just use the value to get the
				// next element
				SymbolicExpression recDomUnion = universe.tupleRead(domValue,
						twoObj);
				SymbolicExpression recDom = universe.unionExtract(zeroObj,
						recDomUnion);

				if (!isAllNull)
					nextEleValues = symbolicUtil.getNextInRectangularDomain(
							recDom, varValues, dim);
				else
					nextEleValues = symbolicUtil.getDomainInit(domValue);
			} else
				throw new CIVLExecutionException(
						ErrorKind.OTHER,
						Certainty.CONCRETE,
						process,
						"The domian object is neither a literal domain nor a rectangular domain",
						this.symbolicAnalyzer.stateInformation(state), source);
		} catch (SARLException | ClassCastException e) {
			throw new CIVLInternalException(
					"Interanl errors happened in executeNextInDomain()", source);
		}
		// Set domain element components one by one.(Domain element is an array
		// of integers of length 'dim')
		for (int i = 0; i < dim; i++)
			state = stateFactory.setVariable(state, loopVars.get(i), pid,
					nextEleValues.get(i));
		// TODO: why set location here ?
		state = stateFactory.setLocation(state, pid, nextInDomain.target());
		return state;
	}

	@Override
	public State execute_printf(CIVLSource source, State state, int pid,
			String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		StringBuffer stringOfSymbolicExpression;
		StringBuffer formatBuffer;
		List<StringBuffer> printedContents = new ArrayList<>();
		Triple<State, StringBuffer, Boolean> concreteString;
		List<Format> formats;
		List<Format> nonVoidFormats = new ArrayList<>();

		concreteString = this.evaluator.getString(arguments[0].getSource(),
				state, process, arguments[0], argumentValues[0]);
		formatBuffer = concreteString.second;
		state = concreteString.first;
		formats = this.splitFormat(arguments[0].getSource(), formatBuffer);
		for (Format format : formats) {
			if (format.type != ConversionType.VOID)
				nonVoidFormats.add(format);
		}
		assert nonVoidFormats.size() == argumentValues.length - 1;
		for (int i = 1; i < argumentValues.length; i++) {
			SymbolicExpression argumentValue = argumentValues[i];
			CIVLType argumentType = arguments[i].getExpressionType();

			if (argumentType instanceof CIVLPointerType
					&& ((CIVLPointerType) argumentType).baseType().isCharType()
					&& argumentValue.operator() == SymbolicOperator.CONCRETE) {
				Format myFormat = nonVoidFormats.get(i - 1);

				if (myFormat.type == ConversionType.STRING) {
					concreteString = this.evaluator.getString(
							arguments[i].getSource(), state, process,
							arguments[i], argumentValue);
					stringOfSymbolicExpression = concreteString.second;
					state = concreteString.first;
					printedContents.add(stringOfSymbolicExpression);
				} else if (myFormat.type == ConversionType.POINTER) {
					printedContents.add(new StringBuffer(symbolicAnalyzer
							.symbolicExpressionToString(
									arguments[i].getSource(), state, null,
									argumentValue)));
				} else {
					throw new CIVLSyntaxException("Array pointer unaccepted",
							arguments[i].getSource());
				}

			} else if (argumentType instanceof CIVLPointerType
					&& this.symbolicUtil.isNullPointer(argumentValue)
					&& nonVoidFormats.get(i - 1).type == ConversionType.INT) {
				printedContents.add(new StringBuffer("0"));
			} else
				printedContents.add(new StringBuffer(this.symbolicAnalyzer
						.symbolicExpressionToString(arguments[i].getSource(),
								state, null, argumentValue)));
		}
		this.printf(civlConfig.out(), arguments[0].getSource(), process,
				formats, printedContents);
		return state;
	}

	/**
	 * Parses the format string, according to C11 standards. For example,
	 * <code>"This is process %d.\n"</code> will be parsed into a list of
	 * strings: <code>"This is process "</code>, <code>"%d"</code>,
	 * <code>".\n"</code>.<br>
	 * 
	 * In Paragraph 4, Section 7.21.6.1, C11 Standards:<br>
	 * Each conversion specification is introduced by the character %. After the
	 * %, the following appear in sequence:
	 * <ul>
	 * <li>Zero or more flags (in any order) that modify the meaning of the
	 * conversion specification.</li>
	 * <li>An optional minimum field width. If the converted value has fewer
	 * characters than the field width, it is padded with spaces (by default) on
	 * the left (or right, if the left adjustment flag, described later, has
	 * been given) to the field width. The field width takes the form of an
	 * asterisk * (described later) or a nonnegative decimal integer.</li>
	 * <li>An optional precision that gives the minimum number of digits to
	 * appear for the d, i, o, u, x, and X conversions, the number of digits to
	 * appear after the decimal-point character for a, A, e, E, f, and F
	 * conversions, the maximum number of significant digits for the g and G
	 * conversions, or the maximum number of bytes to be written for s
	 * conversions. The precision takes the form of a period (.) followed either
	 * by an asterisk * (described later) or by an optional decimal integer; if
	 * only the period is specified, the precision is taken as zero. If a
	 * precision appears with any other conversion specifier, the behavior is
	 * undefined.</li>
	 * <li>An optional length modifier that specifies the size of the argument.</li>
	 * <li>A conversion specifier character that specifies the type of
	 * conversion to be applied.</li>
	 * </ul>
	 * 
	 * @param source
	 *            The source code element of the format argument.
	 * @param formatBuffer
	 *            The string buffer containing the content of the format string.
	 * @return A list of string buffers by splitting the format by conversion
	 *         specifiers.
	 */
	@Override
	public List<Format> splitFormat(CIVLSource source, StringBuffer formatBuffer) {
		int count = formatBuffer.length();
		List<Format> result = new ArrayList<>();
		StringBuffer stringBuffer = new StringBuffer();
		boolean inConversion = false;
		boolean hasFieldWidth = false;
		boolean hasPrecision = false;

		for (int i = 0; i < count; i++) {
			Character current = formatBuffer.charAt(i);
			Character code;
			ConversionType type = ConversionType.VOID;

			if (current.equals('%')) {
				code = formatBuffer.charAt(i + 1);

				if (code.equals('%')) {
					stringBuffer.append("%%");
					i = i + 1;
					continue;
				}
				if (stringBuffer.length() > 0) {
					if (stringBuffer.charAt(0) == '%'
							&& stringBuffer.charAt(1) != '%') {
						throw new CIVLSyntaxException("The format %"
								+ stringBuffer + " is not allowed in fprintf",
								source);
					}
					result.add(new Format(stringBuffer, type));
					stringBuffer = new StringBuffer();
				}
				inConversion = true;
				stringBuffer.append('%');
				current = formatBuffer.charAt(++i);
			}
			if (inConversion) {
				// field width
				if (current.equals('*')) {
					stringBuffer.append('*');
					current = formatBuffer.charAt(++i);
				} else if (numbers.contains(current)) {
					Character next = current;

					if (hasFieldWidth) {
						stringBuffer.append(next);
						throw new CIVLSyntaxException(
								"Duplicate field width in \"" + stringBuffer
										+ "\"...", source);
					}
					hasFieldWidth = true;
					while (numbers.contains(next)) {
						stringBuffer.append(next);
						next = formatBuffer.charAt(++i);
					}
					current = next;
				}
				// precision
				if (current.equals('.')) {
					Character next;

					next = formatBuffer.charAt(++i);
					stringBuffer.append('.');
					if (hasPrecision) {
						throw new CIVLSyntaxException(
								"Duplicate precision detected in \""
										+ stringBuffer + "\"...", source);
					}
					hasPrecision = true;
					if (next.equals('*')) {
						stringBuffer.append(next);
						next = formatBuffer.charAt(++i);
					} else {
						while (numbers.contains(next)) {
							stringBuffer.append(next);
							next = formatBuffer.charAt(++i);
						}
					}
					current = next;
				}
				// length modifier
				switch (current) {
				case 'h':
				case 'l':
					stringBuffer.append(current);
					if (i + 1 >= count)
						throw new CIVLSyntaxException("The format "
								+ stringBuffer + " is not allowed.", source);
					else {
						Character next = formatBuffer.charAt(i + 1);

						if (next.equals(current)) {
							i++;
							stringBuffer.append(next);
						}
						current = formatBuffer.charAt(++i);
					}
					break;
				case 'j':
				case 'z':
				case 't':
				case 'L':
					stringBuffer.append(current);
					current = formatBuffer.charAt(++i);
					break;
				default:
				}
				// conversion specifier
				switch (current) {
				case 'c':
				case 'p':
				case 'n':
					if (hasFieldWidth || hasPrecision) {
						throw new CIVLSyntaxException(
								"Invalid precision for the format \"%"
										+ current + "\"...", source);
					}
				default:
				}
				switch (current) {
				case 'c':
					type = ConversionType.CHAR;
					break;
				case 'p':
				case 'n':
					type = ConversionType.POINTER;
					break;
				case 'd':
				case 'i':
				case 'o':
				case 'u':
				case 'x':
				case 'X':
					type = ConversionType.INT;
					break;
				case 'a':
				case 'A':
				case 'e':
				case 'E':
				case 'f':
				case 'F':
				case 'g':
				case 'G':
					type = ConversionType.DOUBLE;
					break;
				case 's':
					type = ConversionType.STRING;
					break;
				default:
					stringBuffer.append(current);
					throw new CIVLSyntaxException("The format %" + stringBuffer
							+ " is not allowed in fprintf", source);
				}
				stringBuffer.append(current);
				result.add(new Format(stringBuffer, type));
				inConversion = false;
				hasFieldWidth = false;
				hasPrecision = false;
				stringBuffer = new StringBuffer();
			} else {
				stringBuffer.append(current);
			}
		}
		if (stringBuffer.length() > 0)
			result.add(new Format(stringBuffer, ConversionType.VOID));
		return result;
	}

	@Override
	public void printf(PrintStream printStream, CIVLSource source,
			String process, List<Format> formats, List<StringBuffer> arguments) {
		int argIndex = 0;
		int numArguments = arguments.size();

		for (Format format : formats) {
			String formatString = format.toString();

			switch (format.type) {
			case VOID:
				printStream.print(formatString);
				break;
			default:
				assert argIndex < numArguments;
				printStream.printf("%s", arguments.get(argIndex++));
			}
		}

	}

	/**
	 * TODO
	 * 
	 * @param source
	 * @param state
	 * @param pointer
	 * @param value
	 * @param isInitialization
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State assign(CIVLSource source, State state, String process,
			SymbolicExpression pointer, SymbolicExpression value,
			boolean isInitialization)
			throws UnsatisfiablePathConditionException {
		if (!symbolicUtil.isDerefablePointer(pointer)) {
			errorLogger.logSimpleError(source, state, process,
					symbolicAnalyzer.stateInformation(state),
					ErrorKind.DEREFERENCE,
					"attempt to write to a memory location through a pointer "
							+ "that can't be dereferenced");
			throw new UnsatisfiablePathConditionException();
		} else {
			int vid = symbolicUtil.getVariableId(source, pointer);
			int sid = symbolicUtil.getDyscopeId(source, pointer);
			ReferenceExpression symRef = symbolicUtil.getSymRef(pointer);
			State result;
			Variable variable;
			Evaluation eval;

			eval = evaluator.dereference(source, state, process, null, pointer,
					false);
			state = eval.state;

			if (sid < 0) {
				errorLogger
						.logSimpleError(source, state, process,
								symbolicAnalyzer.stateInformation(state),
								ErrorKind.DEREFERENCE,
								"Attempt to dereference pointer into scope which has been removed from state");
				throw new UnsatisfiablePathConditionException();
			}
			variable = state.getDyscope(sid).lexicalScope().variable(vid);
			if (!isInitialization) {
				if (variable.isInput()) {
					errorLogger.logSimpleError(
							source,
							state,
							process,
							symbolicAnalyzer.stateInformation(state),
							ErrorKind.INPUT_WRITE,
							"Attempt to write to input variable "
									+ variable.name());
					throw new UnsatisfiablePathConditionException();
				} else if (variable.isConst()) {
					errorLogger.logSimpleError(
							source,
							state,
							process,
							symbolicAnalyzer.stateInformation(state),
							ErrorKind.CONSTANT_WRITE,
							"Attempt to write to constant variable "
									+ variable.name());
					throw new UnsatisfiablePathConditionException();
				}
			}
			if (symRef.isIdentityReference()) {
				result = stateFactory.setVariable(state, vid, sid, value);
			} else {
				SymbolicExpression oldVariableValue = state.getVariableValue(
						sid, vid);

				try {
					SymbolicExpression newVariableValue = universe.assign(
							oldVariableValue, symRef, value);

					result = stateFactory.setVariable(state, vid, sid,
							newVariableValue);
				} catch (SARLException e) {
					errorLogger.logSimpleError(source, state, process,
							symbolicAnalyzer.stateInformation(state),
							ErrorKind.DEREFERENCE,
							"Invalid assignment: " + e.getMessage());
					throw new UnsatisfiablePathConditionException();
				}
			}
			return result;
		}
	}

	private State assign(State state, int pid, String process,
			LHSExpression lhs, SymbolicExpression value,
			boolean isInitialization)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluator.reference(state, pid, lhs);

		if (lhs instanceof DotExpression) {
			DotExpression dot = (DotExpression) lhs;

			if (dot.isUnion()) {
				int memberIndex = dot.fieldIndex();

				value = evaluator.universe().unionInject(
						(SymbolicUnionType) (dot.structOrUnion()
								.getExpressionType().getDynamicType(evaluator
								.universe())),
						evaluator.universe().intObject(memberIndex), value);
			}
		}
		// TODO check if lhs is constant or input value
		return assign(lhs.getSource(), eval.state, process, eval.value, value,
				isInitialization);
	}

	/* *********************** Methods from Executor *********************** */

	@Override
	public State assign(CIVLSource source, State state, String process,
			SymbolicExpression pointer, SymbolicExpression value)
			throws UnsatisfiablePathConditionException {
		return this.assign(source, state, process, pointer, value, false);
	}

	@Override
	public State assign(State state, int pid, String process,
			LHSExpression lhs, SymbolicExpression value)
			throws UnsatisfiablePathConditionException {
		return this.assign(state, pid, process, lhs, value, false);
	}

	@Override
	public Evaluator evaluator() {
		return evaluator;
	}

	@Override
	public long getNumSteps() {
		return numSteps;
	}

	@Override
	public State malloc(CIVLSource source, State state, int pid,
			String process, LHSExpression lhs, Expression scopeExpression,
			SymbolicExpression scopeValue, CIVLType objectType,
			SymbolicExpression objectValue)
			throws UnsatisfiablePathConditionException {
		Pair<State, SymbolicExpression> mallocResult = this.malloc(source,
				state, pid, process, scopeExpression, scopeValue, objectType,
				objectValue);

		state = mallocResult.left;
		if (lhs != null)
			state = assign(state, pid, process, lhs, mallocResult.right);
		return state;
	}

	@Override
	public Pair<State, SymbolicExpression> malloc(CIVLSource source,
			State state, int pid, String process, Expression scopeExpression,
			SymbolicExpression scopeValue, CIVLType objectType,
			SymbolicExpression objectValue)
			throws UnsatisfiablePathConditionException {
		int mallocId = typeFactory.getHeapFieldId(objectType);
		int dyscopeID;
		SymbolicExpression heapObject;
		CIVLSource scopeSource = scopeExpression == null ? source
				: scopeExpression.getSource();

		dyscopeID = modelFactory.getScopeId(scopeSource, scopeValue);
		heapObject = universe.array(objectType.getDynamicType(universe),
				Arrays.asList(objectValue));
		return stateFactory.malloc(state, dyscopeID, mallocId, heapObject);
	}

	@Override
	public StateFactory stateFactory() {
		return stateFactory;
	}

	@Override
	public State execute(State state, int pid, Transition transition)
			throws UnsatisfiablePathConditionException {
		AtomicLockAction atomicLockAction = transition.atomicLockAction();

		switch (atomicLockAction) {
		case GRAB:
			state = stateFactory.getAtomicLock(state, pid);
			break;
		case RELEASE:
			state = stateFactory.releaseAtomicLock(state);
			break;
		case NONE:
			break;
		default:
			throw new CIVLUnimplementedFeatureException(
					"Executing a transition with the atomic lock action "
							+ atomicLockAction.toString(), transition
							.statement().getSource());
		}
		state = state.setPathCondition(transition.pathCondition());
		switch (transition.transitionKind()) {
		case NORMAL:
			state = this.executeStatement(state, pid, transition.statement());
			break;
		case NOOP:
			state = this.stateFactory.setLocation(state, pid,
					((NoopTransition) transition).statement().target());
			break;
		default:
			throw new CIVLUnimplementedFeatureException(
					"Executing a transition of kind "
							+ transition.transitionKind(), transition
							.statement().getSource());

		}
		if (transition.simpifyState())
			state = this.stateFactory.simplify(state);
		return state;
	}

	@Override
	public CIVLErrorLogger errorLogger() {
		return this.errorLogger;
	}

	@Override
	public State reportContractViolation(State state, CIVLSource source,
			int place, ResultType resultType, BooleanExpression assertValue,
			Expression violatedCondition, ErrorKind errorKind,
			String groupString) throws UnsatisfiablePathConditionException {
		String format = "Contract violation: \n";
		String mergedStateExplanation = "";
		String process;

		// ErrorKind can be CONTRACT (for regular contract) or MPI (mpi
		// collective contract)
		if (errorKind.equals(ErrorKind.MPI_ERROR)) {
			process = "place: " + place + " in " + groupString;
			mergedStateExplanation = "Note: The state where the violated condition be evaluated is merged from "
					+ "a set of snapshots. PID in this state is indeed the place of the process in the group";
		} else
			process = "pid: " + place;
		format += "[" + process + "]:" + violatedCondition + "\n"
				+ violatedCondition + " is evaluated as " + assertValue + "\n"
				+ mergedStateExplanation;
		return errorLogger.logError(source, state, process,
				symbolicAnalyzer.stateToString(state), assertValue, resultType,
				errorKind, format);
	}
}
