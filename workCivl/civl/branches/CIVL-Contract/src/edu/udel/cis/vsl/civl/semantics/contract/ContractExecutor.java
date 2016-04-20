package edu.udel.cis.vsl.civl.semantics.contract;

import java.util.Arrays;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.config.IF.CIVLConstants;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.mpi.LibmpiExecutor;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.ModelConfiguration;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.contract.FunctionBehavior;
import edu.udel.cis.vsl.civl.model.IF.contract.FunctionContract;
import edu.udel.cis.vsl.civl.model.IF.contract.FunctionContract.ContractKind;
import edu.udel.cis.vsl.civl.model.IF.contract.MPICollectiveBehavior;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression.BINARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.MPIContractExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.MPIContractExpression.MPI_CONTRACT_EXPRESSION_KIND;
import edu.udel.cis.vsl.civl.model.IF.expression.PointerSetExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ContractVerifyStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.MallocStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ReturnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement.StatementKind;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.model.common.ContractTranslator;
import edu.udel.cis.vsl.civl.semantics.IF.ContractConditionGenerator;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryLoaderException;
import edu.udel.cis.vsl.civl.semantics.IF.NoopTransition;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.semantics.IF.Transition;
import edu.udel.cis.vsl.civl.semantics.IF.Transition.AtomicLockAction;
import edu.udel.cis.vsl.civl.semantics.common.CommonExecutor;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.StackEntry;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.state.common.immutable.ImmutableState;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.civl.util.IF.Triple;
import edu.udel.cis.vsl.gmc.ErrorLog;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * Contracts System Specification:<br>
 * <p>
 * A contracted function is a function declared with contracts. A contracted
 * function can be called in a contracts system regardless of the existence of
 * the definition.
 * 
 * A non-contracted function is a function without contracts. A non-contracted
 * function can only be called when it is defined. i.e. there is a definition
 * for the function.
 * 
 * 
 * For contracted functions, the definition will be ignored whenever it is
 * called. For defined non-contracted functions, the contracts system will do
 * symbolic execution for calls on them.
 * </p>
 * 
 * @author ziqing
 *
 */
public class ContractExecutor extends CommonExecutor implements Executor {
	private ContractEvaluator evaluator;

	private StateFactory stateFactory;

	private SymbolicUniverse universe;

	private SymbolicAnalyzer symbolicAnalyzer;

	private CIVLErrorLogger errorLogger;

	// private CIVLConfiguration civlConfig;

	private ModelFactory modelFactory;

	private LibraryExecutorLoader loader;

	private SymbolicUtility symbolicUtil;

	// caching:
	private MPIContractExpression wildcard_mpiemptyIn;
	private MPIContractExpression wildcard_mpiemptyOut;

	public ContractExecutor(ModelFactory modelFactory,
			StateFactory stateFactory, ErrorLog log,
			LibraryExecutorLoader loader, ContractEvaluator evaluator,
			SymbolicAnalyzer symbolicAnalyzer, CIVLErrorLogger errorLogger,
			CIVLConfiguration civlConfig) {
		super(modelFactory, stateFactory, log, loader, evaluator,
				symbolicAnalyzer, errorLogger, civlConfig);
		this.evaluator = evaluator;
		this.stateFactory = stateFactory;
		this.universe = modelFactory.universe();
		this.errorLogger = errorLogger;
		// this.civlConfig = civlConfig;
		this.symbolicAnalyzer = symbolicAnalyzer;
		this.symbolicUtil = evaluator.symbolicUtility();
		this.modelFactory = modelFactory;
		this.loader = loader;
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
			state = executeStatement(state, pid, transition.statement());
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

	/**
	 * Override for using a different method to execute a function call if and
	 * only if the callee function is a contracted function.
	 */
	@Override
	protected State executeStatement(State state, int pid, Statement statement)
			throws UnsatisfiablePathConditionException {
		int processIdentifier = state.getProcessState(pid).identifier();
		String process = "p" + processIdentifier + " (id = " + pid + ")";
		CIVLFunction calledFunction;

		numSteps++;
		switch (statement.statementKind()) {
		case RETURN:
			return executeReturn(state, pid, process,
					(ReturnStatement) statement);
		case CALL_OR_SPAWN:
			// Call on a contracted function will be executed in a
			// contract-system specific semantics: using contracts instead of
			// using the function definition:
			calledFunction = ((CallOrSpawnStatement) statement).function();
			if (!calledFunction.isSystemFunction()) {
				if (calledFunction.isContracted())
					return executeContractedFunctionCall(state, pid, process,
							(CallOrSpawnStatement) statement);
			}
			return super.executeStatement(state, pid, statement);
		case CONTRACT_VERIFY:
			return executeContractVerifyCall(state, pid, process,
					(ContractVerifyStatement) statement);
		default:
			return super.executeStatement(state, pid, statement);
		}
	}

	/**
	 * Override for let it recognize a pointer that cannot be proved as valid.
	 */
	@Override
	protected State assign(CIVLSource source, State state, String process,
			SymbolicExpression pointer, SymbolicExpression value,
			boolean isInitialization)
			throws UnsatisfiablePathConditionException {
		if (pointer.operator().equals(SymbolicOperator.TUPLE))
			return super.assign(source, state, process, pointer, value,
					isInitialization);
		else
			errorLogger.logSimpleError(
					source,
					state,
					process,
					symbolicAnalyzer.stateToString(state),
					ErrorKind.CONTRACT,
					"Attempt to write to a memory location through a pointer "
							+ this.symbolicAnalyzer.symbolicExpressionToString(
									source, state, null, pointer)
							+ "\nwhich can't be proved as a valid pointer.");
		throw new UnsatisfiablePathConditionException();
	}

	/**
	 * Execute a return statement. If the function returns to the root function,
	 * execution terminates. This execution only happens when a given function
	 * has definition but no contracts.
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
		Expression returnedExpr = statement.expression();
		SymbolicExpression returnedValue = null;
		ProcessState processState;
		CIVLFunction function;
		String functionName;

		processState = state.getProcessState(pid);
		function = processState.peekStack().location().function();
		functionName = function.name().name();
		if (function.isAtomicFunction())
			state = stateFactory.leaveAtomic(state, pid);
		if (returnedExpr == null)
			returnedValue = null;
		else {
			Evaluation eval = evaluator.evaluate(state, pid, returnedExpr);

			returnedValue = eval.value;
			state = eval.state;
		}
		// In contracts mode, only function invoked by $contractVerify keyword
		// will reach its' return statement because contracted function call
		// will not be executed in real and non-contracted function call will
		// not get into the following branch:
		if (function.isContracted()) {
			// Assigning \result variable:
			if (returnedValue != null) {
				Variable resultVar;

				resultVar = function.outerScope().variable(
						ContractTranslator.contractResultName);
				if (resultVar != null)
					state = stateFactory.setVariable(state, resultVar, pid,
							returnedValue);
			}
			// Before pop stack entry frame, verify contracts:
			state = verifyContractsAtReturn(state, pid, process, function,
					function.functionContract());
			// Set MPI status to FINALIZED if it exists:
			state = setMPISysStatusIfExists(state, pid, function.outerScope()
					.parent(), evaluator.FINALIZED);
			// Clean heapObjects allocated for "\valid()":
			state = stateFactory.setVariable(state, function.outerScope()
					.variable(0), pid, universe.nullExpression());
		}
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
						throw new UnsatisfiablePathConditionException();
					}
				}
			}
		}
		state = stateFactory.popCallStack(state, pid);
		processState = state.getProcessState(pid);
		if (!processState.hasEmptyStack()) {
			StackEntry returnContext = processState.peekStack();
			Location returnLocation = returnContext.location();
			Statement outgoing = returnLocation.getSoleOutgoing();
			boolean hasLHS;

			// Assigning returned value to LHS:
			if (outgoing.statementKind() == StatementKind.CALL_OR_SPAWN) {
				CallOrSpawnStatement call = (CallOrSpawnStatement) outgoing;

				hasLHS = call.lhs() != null;
				if (hasLHS) {
					if (returnedValue == null) {
						errorLogger
								.logSimpleError(
										call.getSource(),
										state,
										process,
										symbolicAnalyzer
												.stateInformation(state),
										ErrorKind.OTHER,
										"attempt to use the return value of function "
												+ functionName
												+ " when "
												+ functionName
												+ " has returned without a return value.");
						returnedValue = universe.nullExpression();
					}
					state = assign(state, pid, process, call.lhs(),
							returnedValue);
				}
			} else {
				assert outgoing.statementKind() == StatementKind.CONTRACT_VERIFY;
				hasLHS = false;
			}
			state = stateFactory.setLocation(state, pid, outgoing.target(),
					hasLHS);
		}
		return state;
	}

	/**
	 * Execute a contracted function call. The semantics of the execution is
	 * using the contracts of the function to infer the result state instead of
	 * executing the function body normally.
	 * 
	 * The execution conforms the core principal: Requirements hold implies
	 * Ensurances hold.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param call
	 *            The call statement
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeContractedFunctionCall(State state, int pid,
			String process, CallOrSpawnStatement call)
			throws UnsatisfiablePathConditionException {
		// A temporary state which is used to evaluates contracts. A temporary
		// state is the state right after the called function being pushed on to
		// the call stack. Using such a state, the evaluator can evaluates
		// expression involving function parameters:
		State tmpState;
		// Function identifier evaluation
		Triple<State, CIVLFunction, Integer> funcEval;
		SymbolicExpression[] arguments;
		SymbolicConstant tmpRetExpr;
		SymbolicExpression tmpRetVal;
		Variable result;
		CIVLFunction function = call.function();
		String functionName = function.name().name();
		Evaluation eval;

		// Evaluating arguments:
		arguments = new SymbolicExpression[call.arguments().size()];
		for (int i = 0; i < call.arguments().size(); i++) {
			eval = evaluator.evaluate(state, pid, call.arguments().get(i));

			state = eval.state;
			arguments[i] = eval.value;
		}
		funcEval = evaluator.evaluateFunctionIdentifier(state, pid,
				call.functionExpression(), call.getSource());
		tmpState = stateFactory.pushCallStack(state, pid, function,
				funcEval.third, arguments);
		// Make returned value an uninterpreted expression (abstract function
		// call) :
		// TODO: function.functionType parameterTypes may have bug!
		List<SymbolicType> inputTypes = new LinkedList<>();

		for (Variable arg : function.parameters())
			inputTypes.add(arg.type().getDynamicType(universe));
		tmpRetExpr = universe.symbolicConstant(universe.stringObject(function
				.name().name()), universe.functionType(inputTypes, function
				.returnType().getDynamicType(universe)));
		tmpRetVal = universe.apply(tmpRetExpr, Arrays.asList(arguments));
		// Insert the value of \result into the temporary state:
		result = function.outerScope().variable(
				ContractTranslator.contractResultName);
		if (result != null)
			tmpState = stateFactory.setVariable(tmpState, result, pid,
					tmpRetVal);
		// Assign returned value:
		if (call.lhs() != null)
			state = assign(state, pid, process, call.lhs(), tmpRetVal);
		// Deduce contracts:
		// Requirements are checked on the temporary state;
		// Assurances are inferred from current state.
		state = inferByContracts(tmpState, state, pid, process, functionName,
				function.functionContract());
		state = stateFactory.setLocation(state, pid, call.target());
		return state;
	}

	/**
	 * A {@link ContractVerifyStatement} triggers verifying a function
	 * independently. Executes a {@link ContractVerifyStatement} is similar to
	 * execute a function call but the start state of the execution on the
	 * function body is constructed based on the contracts. It simulates the
	 * semantics of verifying a function in isolation.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param conVeri
	 *            The ContractVerifyStatement
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeContractVerifyCall(State state, int pid,
			String process, ContractVerifyStatement conVeri)
			throws UnsatisfiablePathConditionException {
		State tmpState;
		SymbolicExpression[] arguments;
		CIVLFunction function = conVeri.function();
		// Function identifier evaluation
		Triple<State, CIVLFunction, Integer> funcEval;
		Evaluation eval;

		// Evaluating arguments:
		arguments = new SymbolicExpression[conVeri.arguments().size()];
		for (int i = 0; i < conVeri.arguments().size(); i++) {
			eval = evaluator.evaluate(state, pid, conVeri.arguments().get(i));

			state = eval.state;
			arguments[i] = eval.value;
		}
		// Using stateFactory create a temporary state only used for evaluating
		// requirements of contracted functions:
		funcEval = evaluator.evaluateFunctionIdentifier(state, pid,
				conVeri.functionExpression(), conVeri.getSource());
		tmpState = stateFactory.pushCallStack(state, pid, function,
				funcEval.third, arguments);
		tmpState = enterContractVerifyState(tmpState, pid, process, function);
		return tmpState;

	}

	/*********************** Contracts in execution **************************/
	/**
	 * Helper method. Inference using contracts happens when calling a
	 * contracted function. It tests if requirements of the contracts are
	 * satisfied then delivers ensurances of the contracts for the next state as
	 * the state after returning from the called function.
	 * 
	 * @param evalState
	 *            Evaluating state. The caller to this method is responsible for
	 *            providing such evaluating state. Such a state can be obtained
	 *            by pushing a stack frame onto the call stack so that
	 *            evaluators can reach those parameters of the function.
	 * @param realState
	 *            The real current state which should be the state right before
	 *            calling the function.
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param functionName
	 *            The name of the function
	 * @param contract
	 *            The {@link FunctionContracts} of the function.
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State inferByContracts(State evalState, State realState, int pid,
			String process, String functionName, FunctionContract contract)
			throws UnsatisfiablePathConditionException {
		FunctionBehavior defaultBehav;
		BooleanExpression assumptions;

		defaultBehav = contract.defaultBehavior();
		// Verify requirements:
		for (Expression condition : defaultBehav.requirements()) {
			SymbolicExpression reqPred;
			BooleanExpression holdPred;
			Evaluation eval;
			Reasoner reasoner;
			ResultType resultType;

			eval = evaluator.evaluate(evalState, pid, condition);
			evalState = eval.state;
			reqPred = eval.value;
			holdPred = universe.equals(reqPred, universe.trueExpression());
			reasoner = universe.reasoner(evalState.getPathCondition());
			resultType = reasoner.valid(holdPred).getResultType();
			if (!resultType.equals(ResultType.YES)) {
				String message = "Contract condition : " + condition
						+ " is not satisfied when calling function "
						+ functionName;

				realState = errorLogger.logError(condition.getSource(),
						realState, process,
						symbolicAnalyzer.stateToString(realState), holdPred,
						resultType, ErrorKind.CONTRACT, message);
			}
		}
		// Verify mpi requirements collectively:
		for (MPICollectiveBehavior mpiCollective : contract.getMPIBehaviors()) {
			evalState = executeCollectiveChecking(evalState, pid, process,
					mpiCollective.requirements(), mpiCollective.communicator(),
					mpiCollective.getSource());
			realState = stateFactory.copySnapshotsQueues(evalState, realState);
		}
		// Assume ensurances:
		assumptions = conjunctConditions(evalState, pid, process,
				defaultBehav.ensurances());
		realState = realState.setPathCondition(universe.and(
				realState.getPathCondition(), assumptions));
		return realState;
	}

	/**
	 * Helper method. Derive function contracts into canonical boolean
	 * expressions so that these boolean expressions can be reasoned at some
	 * time. e.g. During the symbolic execution, it needs to know weather a
	 * pointer is valid or not, then the query can be encoded into the canonical
	 * boolean expression then let reasoner to use the conditions to prove it.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param function
	 *            The function
	 * @param contracts
	 *            The function contracts
	 * @return The state whose path condition has been updated by the derivation
	 * @throws UnsatisfiablePathConditionException
	 */
	private State deriveContractsAtBegin(State state, int pid, String process,
			CIVLFunction function, FunctionContract contracts)
			throws UnsatisfiablePathConditionException {
		FunctionBehavior defaultBehavior = contracts.defaultBehavior();

		state = deriveConditionsWorker(state, pid, process,
				defaultBehavior.requirements());
		// TODO: it's better to hide the MPI information

		for (MPICollectiveBehavior mpiCollective : contracts.getMPIBehaviors()) {
			Triple<State, SymbolicExpression, SymbolicExpression> eval;

			eval = evaluator.deriveMPICollectiveTitle(state, pid, process,
					mpiCollective, function.outerScope());
			state = eval.first;

			// TODO: currently try not to collectively execute everything but
			// just empty buffer:
			Iterable<Expression> emptyIOs = wildcardMPIEmptyIO(state, pid,
					process, mpiCollective.communicator(),
					mpiCollective.getSource(), function);

			state = executeCollectiveChecking(state, pid, process, emptyIOs,
					mpiCollective.communicator(), mpiCollective.getSource());
			state = deriveConditionsWorker(state, pid, process,
					mpiCollective.requirements());
		}
		return state;
	}

	/**
	 * Helper method. Derive a set of conditions to boolean expressions then
	 * combine them into the path condition of the current state.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param conditions
	 *            A {@link Iterable} set of processes.
	 * @return The state whose path condition has been updated.
	 * @throws UnsatisfiablePathConditionException
	 */
	private State deriveConditionsWorker(State state, int pid, String process,
			Iterable<Expression> conditions)
			throws UnsatisfiablePathConditionException {
		BooleanExpression context = state.getPathCondition();
		Reasoner reasoner = universe.reasoner(context);

		for (Expression condition : conditions) {
			Evaluation eval = evaluator.deriveExpression(state, pid, condition);

			state = eval.state;
			context = universe.and(context, (BooleanExpression) eval.value);
		}
		context = reasoner.simplify(context);
		return state.setPathCondition(context);
	}

	/**
	 * An helper method which should be called when a function invoked by a
	 * {link ContractVerifyStatement} is returned. Currently,
	 * {@link FunctionContract#defaultBehavior()} will be verified. It checks if
	 * conditions of {@link FunctionBehavior#ensurances()} hold.
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param function
	 *            The function
	 * @param contracts
	 *            The function contracts
	 * @return The state after this checking.
	 * @throws UnsatisfiablePathConditionException
	 */
	private State verifyContractsAtReturn(State state, int pid, String process,
			CIVLFunction function, FunctionContract contracts)
			throws UnsatisfiablePathConditionException {
		FunctionBehavior defaultBehavior = contracts.defaultBehavior();

		state = verifyConditionsAtReturnWorker(state, pid, process,
				defaultBehavior.ensurances(), function.name().name());
		// TODO: it's better to hide the MPI information
		for (MPICollectiveBehavior mpiCollective : contracts.getMPIBehaviors()) {
			Iterable<Expression> wildcardEmptyIO = this.wildcardMPIEmptyIO(
					state, pid, process, mpiCollective.communicator(),
					mpiCollective.getSource(), function);

			state = executeCollectiveChecking(state, pid, process,
					wildcardEmptyIO, mpiCollective.communicator(),
					mpiCollective.getSource());
			state = verifyConditionsAtReturnWorker(state, pid, process,
					mpiCollective.ensurances(), function.name().name());
		}
		return state;
	}

	/**
	 * The worker method of
	 * {@link #verifyContractsAtReturn(State, int, String, CIVLFunction, FunctionContract)}
	 * . This method tests a set condition expressions if they are hold at the
	 * current state.
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param conditions
	 *            The {@link Iterable} set of conditions
	 * @param functionName
	 *            The name of the function, used to error reporting
	 * @return The state after testing.
	 * @throws UnsatisfiablePathConditionException
	 */
	private State verifyConditionsAtReturnWorker(State state, int pid,
			String process, Iterable<Expression> conditions, String functionName)
			throws UnsatisfiablePathConditionException {

		for (Expression condition : conditions) {
			SymbolicExpression reqPred;
			BooleanExpression holdPred;
			Evaluation eval;
			Reasoner reasoner;

			eval = evaluator.evaluate(state, pid, condition);
			state = eval.state;
			reqPred = eval.value;
			holdPred = universe.equals(reqPred, universe.trueExpression());
			reasoner = universe.reasoner(state.getPathCondition());
			if (!reasoner.isValid(holdPred)) {
				String message = "Contract condition : " + condition
						+ " is not satisfied when calling function "
						+ functionName;

				state = errorLogger.logError(condition.getSource(), state,
						process, symbolicAnalyzer.stateToString(state),
						holdPred, ResultType.NO, ErrorKind.CONTRACT, message);
			}
		}
		return state;
	}

	/****************** Constructing Contract Start State ********************/
	/**
	 * This method is responsible for constructing an isolated start environment
	 * for a function invoked by a {@link ContractVerifyStatement}. The
	 * environment is built based on CIVL contract system semantics and the
	 * contracts of the function.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param function
	 *            The function
	 * @return The start state of the execution of the function body.
	 * @throws UnsatisfiablePathConditionException
	 */
	private State enterContractVerifyState(State state, int pid,
			String process, CIVLFunction function)
			throws UnsatisfiablePathConditionException {
		// initialize all visible variables
		Scope outScope = function.outerScope().parent();
		Evaluation eval;

		while (outScope != null) {
			Set<Variable> variables = outScope.variables();
			int dyscope = state.getDyscope(pid, outScope);

			// TODO: need a don't touch list
			// Don't initialize unreachable variables:
			if (state.reachableByProcess(dyscope, pid)) {
				for (Variable var : variables) {
					if (var.vid() != 0 && canIInitThisVariable(outScope, var)) {
						if (var.type().isPointerType()) {
							Expression initVar;

							var.setIsInput(true);
							initVar = modelFactory.initialValueExpression(
									var.getSource(), var);
							eval = evaluator.evaluate(state, pid, initVar);
							var.setIsInput(false);
						} else
							eval = evaluator.havoc(state, var.type()
									.getDynamicType(universe));
						state = eval.state;
						state = stateFactory.setVariable(state, var, pid,
								eval.value);
					}
				}
			}
			outScope = outScope.parent();
		}

		// Initialize pointer type parameters:
		Iterator<Variable> paraIter = function.parameters().iterator();

		while (paraIter.hasNext()) {
			Expression initVar;

			Variable para = paraIter.next();

			if (para.type().isPointerType()) {
				para.setIsInput(true);
				initVar = modelFactory.initialValueExpression(para.getSource(),
						para);
				eval = evaluator.evaluate(state, pid, initVar);
				para.setIsInput(false);
				state = eval.state;
				state = stateFactory.setVariable(state, para, pid, eval.value);
			}
		}
		// Set $mpi_sys_status to INITIALIZED it it exists:
		state = setMPISysStatusIfExists(state, pid, function.outerScope()
				.parent(), evaluator.INITIALIZED);
		/******* Necessary derivation on contracts *******/
		// PHASE 1: Derives contracts to reasonable boolean expressions:
		Iterator<Expression> requiresIter;
		BooleanExpression context = universe.trueExpression();
		FunctionContract contracts = function.functionContract();
		ContractConditionGenerator conditionGenerator = evaluator
				.contractConditionGenerator();
		List<Pair<PointerSetExpression, Integer>> validConsequences = new LinkedList<>();

		requiresIter = contracts.defaultBehavior().requirements().iterator();
		while (requiresIter.hasNext()) {
			eval = conditionGenerator.deriveExpression(state, pid,
					requiresIter.next());
			state = (ImmutableState) eval.state;
			context = universe.and(context, (BooleanExpression) eval.value);
		}
		state = deriveContractsAtBegin(state, pid, process, function, contracts);
		// PHASE 2: Reasoning some clauses that need special handling:
		// TODO: reasoning is depend on process but current valid consequences
		// are not stored by PID
		for (Pair<Expression, Integer> guess : function
				.getPossibleValidConsequences()) {
			PointerSetExpression mem;

			eval = conditionGenerator.deriveExpression(state, pid, guess.left);
			state = (ImmutableState) eval.state;
			if (isRequirementConsequence(context,
					(BooleanExpression) eval.value)) {
				mem = (PointerSetExpression) ((UnaryExpression) guess.left)
						.operand();
				validConsequences.add(new Pair<>(mem, guess.right));
			}
		}

		// PHASE 2.1 Special handling on some clauses:
		conditionGenerator.setValidConsequences(validConsequences);
		state = concretizeAllPointers(state, pid, function, conditionGenerator);

		// PHASE 3: Evaluating contracts phase:
		Reasoner reasoner;

		context = state.getPathCondition();
		requiresIter = contracts.defaultBehavior().requirements().iterator();
		while (requiresIter.hasNext()) {
			BooleanExpression pred;
			Expression require = requiresIter.next();

			eval = evaluator.evaluate(state, pid, require);
			state = (ImmutableState) eval.state;
			reasoner = universe.reasoner(context);
			pred = (BooleanExpression) eval.value;
			context = universe.and(context, pred);
			if (reasoner.getReducedContext().isFalse()) {
				SymbolicAnalyzer symbolicAnalyzer = evaluator
						.symbolicAnalyzer();

				evaluator.errorLogger().logSimpleError(require.getSource(),
						state, process,
						symbolicAnalyzer.stateInformation(state),
						ErrorKind.CONTRACT,
						"Unsatisfiable requirements: " + require);
			}
		}
		state = state.setPathCondition(context);
		return state;
		// return stateFactory.canonic(state, false, false, false, null);
	}

	private boolean isRequirementConsequence(BooleanExpression context,
			BooleanExpression consequence) {
		Reasoner reasoner;
		// Inference on consequences of requirements doesn't need path
		// conditions:
		reasoner = universe.reasoner(context);
		return reasoner.isValid(consequence);
	}

	private ImmutableState concretizeAllPointers(State state, int pid,
			CIVLFunction function, ContractConditionGenerator conditionGenerator)
			throws UnsatisfiablePathConditionException {
		Iterator<List<Integer>> mallocsIter = conditionGenerator
				.validPointersIterator();
		int processIdentifier = state.getProcessState(pid).identifier();
		String process = "p" + processIdentifier + " (id = " + pid + ")";
		Evaluation eval;

		while (mallocsIter.hasNext()) {
			List<Integer> mallocIDs = mallocsIter.next();
			Scope scope = function.outerScope();
			int dyscopeId = state.getDyscope(pid, scope);

			for (Integer i : mallocIDs) {
				MallocStatement mallocStmt = modelFactory.model().getMalloc(i);
				SymbolicExpression range;
				NumericExpression size;
				Pair<State, SymbolicExpression> ret;

				if (mallocStmt.getSizeExpression() != null) {
					eval = evaluator.evaluate(state, pid,
							mallocStmt.getSizeExpression());
					state = eval.state;
					range = eval.value;
					size = symbolicUtil.getHighOfRegularRange(range);
					// \valid(ptr + (0..n)) ==> there are (n + 1) objects in
					// heap:
					size = universe.add(size, universe.oneInt());
				} else
					size = universe.oneInt();
				ret = stateFactory.malloc(state, pid, dyscopeId, i,
						mallocStmt.getDynamicElementType(), size);
				state = ret.left;
				state = assign(state, pid, process, mallocStmt.getLHS(),
						ret.right);
			}
		}
		return (ImmutableState) state;
	}

	// Set $mpi_sys_status to FINALIZED it it exists:
	// Scope outer = functionOuter.parent();
	//
	// while (outer != null) {
	// Variable mpiSysStatus = outer
	// .variable(ModelConfiguration.MPI_SYS_STATUS);
	//
	// if (mpiSysStatus != null) {
	// state = stateFactory.setVariable(state, mpiSysStatus, pid,
	// FINALIZED);
	// break;
	// } else
	// outer = outer.parent();
	// }

	private State setMPISysStatusIfExists(State state, int pid, Scope outer,
			NumericExpression status) {
		while (outer != null) {
			Variable mpiSysStatus = outer
					.variable(ModelConfiguration.MPI_SYS_STATUS);

			if (mpiSysStatus != null) {
				state = stateFactory.setVariable(state, mpiSysStatus, pid,
						status);
				break;
			} else
				outer = outer.parent();
		}
		return state;
	}

	private State executeCollectiveChecking(State state, int pid,
			String process, Iterable<Expression> conditions,
			Expression communicator, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		Expression[] args = new Expression[2];
		LibmpiExecutor mpiExecutor;

		// Creating an entry
		try {
			mpiExecutor = (LibmpiExecutor) loader.getLibraryExecutor("mpi",
					this, modelFactory, symbolicUtil, symbolicAnalyzer);
			args[0] = communicator;
			// TODO: make a helper method:
			args[1] = modelFactory.trueExpression(communicator.getSource());
			for (Expression requires : conditions)
				args[1] = modelFactory.binaryExpression(
						modelFactory.sourceOfSpan(args[1].getSource(),
								requires.getSource()), BINARY_OPERATOR.AND,
						args[1], requires);
			return mpiExecutor.executeCollectiveContract(state, pid, process,
					args, ContractKind.REQUIRES, source);
		} catch (LibraryLoaderException e) {
			StringBuffer message = new StringBuffer();

			message.append("unable to load the library evaluator for the library ");
			message.append("mpi");
			message.append(" for the \\mpi_collective(...) contracts ");
			errorLogger.logSimpleError(source, state, process,
					this.symbolicAnalyzer.stateInformation(state),
					ErrorKind.LIBRARY, message.toString());
			throw new UnsatisfiablePathConditionException();
		}
	}

	/**
	 * Helper method. Creates and caches wildcard \mpi_empty_in and
	 * \mpi_empty_out expressions.
	 * 
	 * @param state
	 * @param pid
	 * @param process
	 * @param communicator
	 * @param source
	 * @param function
	 * @return
	 */
	private Iterable<Expression> wildcardMPIEmptyIO(State state, int pid,
			String process, Expression communicator, CIVLSource source,
			CIVLFunction function) {
		Expression[] argument = new Expression[1];

		if (this.wildcard_mpiemptyIn == null
				|| this.wildcard_mpiemptyOut == null) {
			argument[0] = modelFactory.wildcardExpression(null, modelFactory
					.typeFactory().integerType());
			wildcard_mpiemptyIn = modelFactory.mpiContractExpression(source,
					function.outerScope(), communicator, argument,
					MPI_CONTRACT_EXPRESSION_KIND.MPI_EMPTY_IN);
			wildcard_mpiemptyOut = modelFactory.mpiContractExpression(source,
					function.outerScope(), communicator, argument,
					MPI_CONTRACT_EXPRESSION_KIND.MPI_EMPTY_OUT);
		}
		return Arrays.asList(wildcard_mpiemptyIn, wildcard_mpiemptyOut);
	}

	/**
	 * Helper function. A set of expressions will be evaluated and their results
	 * will be conjuncted as a whole boolean expression.
	 * 
	 * <p>
	 * Pre-conditions: input conditions must be boolean expressions.
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param conditions
	 *            A set of {@link Iterable} conditions
	 * @return The conjunction of results.
	 * @throws UnsatisfiablePathConditionException
	 */
	private BooleanExpression conjunctConditions(State state, int pid,
			String process, Iterable<Expression> conditions)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression ensPred;
		Evaluation eval;
		BooleanExpression newContext = universe.trueExpression();

		for (Expression condition : conditions) {
			eval = evaluator.evaluate(state, pid, condition);
			state = eval.state;
			ensPred = eval.value;
			newContext = (BooleanExpression) universe.canonic(universe.and(
					newContext, (BooleanExpression) ensPred));
		}
		return newContext;
	}

	// TODO: completes this. Currently it just ignores all variables created by
	// CIVL that is ones whose name starts with an underscore.
	private boolean canIInitThisVariable(Scope scope, Variable var) {
		String varName = var.name().name();

		if (varName.startsWith("_"))
			return false;
		switch (varName) {
		case ModelConfiguration.GENERAL_ROOT:
		case ModelConfiguration.SYMBOLIC_CONSTANT_COUNTER:
		case ModelConfiguration.SYMBOLIC_INPUT_COUNTER:
		case ModelConfiguration.ATOMIC_LOCK_VARIABLE:
		case ModelConfiguration.TIME_COUNT_VARIABLE:
		case ModelConfiguration.GCOMM_WORLD:
		case ModelConfiguration.GCOMMS:
		case ModelConfiguration.COMM_WORLD:
		case ModelConfiguration.MPI_SYS_STATUS:
		case ModelConfiguration.NPROCS:
		case ModelConfiguration.NPROCS_LOWER_BOUND:
		case ModelConfiguration.NPROCS_UPPER_BOUND:
			return false;
		default:
			return true;
		}
	}
}
