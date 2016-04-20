package edu.udel.cis.vsl.civl.semantics.contract;

import java.util.Arrays;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.contract.FunctionContract;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ReturnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.model.common.ContractTranslator;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
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
import edu.udel.cis.vsl.civl.util.IF.Triple;
import edu.udel.cis.vsl.gmc.ErrorLog;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
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

	// private LibraryExecutorLoader loader;

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
		// this.symbolicUtil = evaluator.symbolicUtility();
		this.modelFactory = modelFactory;
		// this.loader = loader;
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

		numSteps++;
		// Statements that should be executed in a contracts-system specific
		// semantics:
		switch (statement.statementKind()) {
		case RETURN:
			// TODO:Experimental:
			CIVLFunction currentFunction = state.getProcessState(pid)
					.peekStack().location().function();

			if (currentFunction.isContracted())
				return executeReturn(state, pid, process,
						(ReturnStatement) statement);
			else
				return super.executeStatement(state, pid, statement);
		case CALL_OR_SPAWN:// TODO: need check if contracted
			if (((CallOrSpawnStatement) statement).function().isContracted())
				return executeContractedFunctionCall(state, pid, process,
						(CallOrSpawnStatement) statement);
		default:
			return super.executeStatement(state, pid, statement);
		}

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
		SymbolicExpression returnValue;
		ProcessState processState;
		CIVLFunction function;
		String functionName;
		Iterable<Expression> assurances;

		processState = state.getProcessState(pid);
		function = processState.peekStack().location().function();
		functionName = function.name().name();
		// Assigning \result variable:
		if (returnedExpr == null)
			returnValue = null;
		else {
			Evaluation eval = evaluator.evaluate(state, pid, returnedExpr);
			Variable resultVar;

			returnValue = eval.value;
			state = eval.state;
			resultVar = function.outerScope().variable(
					ContractTranslator.contractResultName);
			if (resultVar != null)
				state = stateFactory.setVariable(state, resultVar, pid,
						returnValue);
		}
		// Before pop stack entry frame, verify assurances:
		assurances = function.functionContract().defaultBehavior().ensurances();
		for (Expression ens : assurances) {
			Evaluation eval;
			BooleanExpression ensPred, holdPred;
			Reasoner reasoner = universe.reasoner(state.getPathCondition());
			ResultType resultType;

			eval = evaluator.evaluate(state, pid, ens);
			state = eval.state;
			ensPred = (BooleanExpression) eval.value;
			holdPred = universe.equals(ensPred, universe.trueExpression());
			reasoner = universe.reasoner(state.getPathCondition());
			resultType = reasoner.valid(holdPred).getResultType();
			if (!resultType.equals(ResultType.YES)) {
				String message = "Assurance : " + ens
						+ " is not satisfied after returning from function "
						+ function.name() + ".";

				state = errorLogger.logError(ens.getSource(), state, process,
						symbolicAnalyzer.stateToString(state), holdPred,
						resultType, ErrorKind.CONTRACT, message);
			}
		}
		// clean: heapObject allocated for "\valid()":
		state = stateFactory.setVariable(state,
				function.outerScope().variable(0), pid,
				universe.nullExpression());
		state = stateFactory.popCallStack(state, pid);
		processState = state.getProcessState(pid);
		if (!processState.hasEmptyStack()) {
			StackEntry returnContext = processState.peekStack();
			Location returnLocation = returnContext.location();

			if (function.name().equals(evaluator.getVerifyingFunction().name())) {
				// If the caller function is root function, execution
				// terminates:
				if (!modelFactory.isPocessIdDefined(pid)
						|| modelFactory.isProcessIdNull(pid))
					return state;
				else
					// there should be no any call stack entry, pop until empty:
					while (!state.getProcessState(pid).hasEmptyStack())
						state = stateFactory.popCallStack(state, pid);
				return state;
			} else {
				CallOrSpawnStatement call = (CallOrSpawnStatement) returnLocation
						.getSoleOutgoing();

				if (call.lhs() != null) {
					if (returnValue == null) {
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
						returnValue = universe.nullExpression();
					}
					state = assign(state, pid, process, call.lhs(), returnValue);
				}
				state = stateFactory.setLocation(state, pid, call.target(),
						call.lhs() != null);
			}
		}
		return state;
	}

	/**
	 * Execute a contracted function call, requirements hold implies ensures
	 * hold.
	 * 
	 * @param state
	 * @param pid
	 * @param call
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */

	// state ==> tmpState : check requirements
	// || =======> state : imply assurances
	private State executeContractedFunctionCall(State state, int pid,
			String process, CallOrSpawnStatement call)
			throws UnsatisfiablePathConditionException {
		State tmpState;
		SymbolicExpression[] arguments;
		SymbolicConstant tmpRetExpr;
		SymbolicExpression tmpRetVal;
		Variable result;
		CIVLFunction function = call.function();
		String functionName = function.name().name();
		// Function identifier evaluation
		Triple<State, CIVLFunction, Integer> funcEval;
		Evaluation eval;

		// Evaluating arguments:
		arguments = new SymbolicExpression[call.arguments().size()];
		for (int i = 0; i < call.arguments().size(); i++) {
			eval = evaluator.evaluate(state, pid, call.arguments().get(i));

			state = eval.state;
			arguments[i] = eval.value;
		}
		// Using stateFactory create a temporary state only used for evaluating
		// requirements of contracted functions:
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
		// result = modelFactory.variable(source, type, name, vid);
		result = function.outerScope().variable(
				ContractTranslator.contractResultName);
		tmpState = stateFactory.setVariable(tmpState, result, pid, tmpRetVal);
		// Assign returned value:
		if (call.lhs() != null)
			state = assign(state, pid, process, call.lhs(), tmpRetVal);
		// Deduce contracts:
		// Requirements are checked on the temporary state;
		// Assurances are inferred from current state.
		state = deduceContract(tmpState, state, pid, process, functionName,
				function.functionContract());
		state = stateFactory.simplify(state);
		state = stateFactory.setLocation(state, pid, call.target());
		return state;
	}

	private State deduceContract(State evalState, State realState, int pid,
			String process, String functionName, FunctionContract contract)
			throws UnsatisfiablePathConditionException {
		// Requirements:
		realState = deduceRequirement(evalState, realState, pid, process,
				functionName, contract.defaultBehavior().requirements());
		// Ensureances:
		realState = deduceAssurance(evalState, realState, pid, process,
				contract.defaultBehavior().ensurances());
		return realState;
	}

	/**
	 * TODO: Doc
	 * 
	 * @param evalState
	 * @param realState
	 * @param pid
	 * @param process
	 * @param functionName
	 * @param reqs
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State deduceRequirement(State evalState, State realState, int pid,
			String process, String functionName, Iterable<Expression> reqs)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression reqPred;
		BooleanExpression holdPred;
		Evaluation eval;
		Reasoner reasoner;
		Iterator<Expression> reqsIter = reqs.iterator();

		while (reqsIter.hasNext()) {
			Expression reqExpr = reqsIter.next();

			eval = evaluator.evaluate(evalState, pid, reqExpr);
			evalState = eval.state;
			reqPred = eval.value;
			holdPred = universe.equals(reqPred, universe.trueExpression());
			reasoner = universe.reasoner(evalState.getPathCondition());
			if (!reasoner.isValid(holdPred)) {
				String message = "Requirement : " + reqExpr
						+ " is not satisfied when calling function "
						+ functionName;

				realState = errorLogger.logError(reqExpr.getSource(),
						realState, process,
						symbolicAnalyzer.stateToString(realState), holdPred,
						ResultType.NO, ErrorKind.CONTRACT, message);
			}
		}
		return realState;
	}

	// TODO:doc
	private State deduceAssurance(State evalState, State realState, int pid,
			String process, Iterable<Expression> ensurances)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression ensPred;
		Evaluation eval;
		BooleanExpression newPathCondition = universe.trueExpression();
		Iterator<Expression> ensIter = ensurances.iterator();

		while (ensIter.hasNext()) {
			Expression ensurance = ensIter.next();

			eval = evaluator.evaluate(evalState, pid, ensurance);
			evalState = eval.state;
			ensPred = eval.value;
			newPathCondition = (BooleanExpression) universe.canonic(universe
					.and(realState.getPathCondition(),
							(BooleanExpression) ensPred));
		}
		return realState.setPathCondition(newPathCondition);
	}

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
					"attempt to write to a memory location through a pointer "
							+ this.symbolicAnalyzer.symbolicExpressionToString(
									source, state, null, pointer)
							+ "\nwhich can't be proved as a valid pointer.");
		throw new UnsatisfiablePathConditionException();
	}

	// // TODO:exprimental
	// public State initializeMPICOMMWORLD(State state, int pid,
	// LHSExpression lhs, int numProcesses, Location location, Scope scope)
	// throws UnsatisfiablePathConditionException {
	// LibcommExecutor commExecutor = null;
	// CallOrSpawnStatement statement;
	// CIVLFunction function;
	// Expression scopeExpr, nprocsExpr, arguments[], funcExpr;
	// Variable nprocs, genRoot;
	//
	// arguments = new Expression[2];
	// nprocs = scope.variable("_mpi_nprocs");
	// nprocsExpr = modelFactory
	// .variableExpression(nprocs.getSource(), nprocs);
	// scopeExpr = modelFactory.hereOrRootExpression(null, true);
	// arguments[0] = scopeExpr;
	// arguments[1] = nprocsExpr;
	// function = modelFactory.model().function("$mpi_gcomm_create");
	// funcExpr = modelFactory.functionIdentifierExpression(null, function);
	// statement = modelFactory.callOrSpawnStatement(null, location, true,
	// funcExpr, Arrays.asList(arguments), null);
	// statement.setTarget(location);
	// statement.setLhs(lhs);
	// try {
	// commExecutor = (LibcommExecutor) loader.getLibraryExecutor("comm",
	// this, modelFactory, evaluator.symbolicUtility(),
	// symbolicAnalyzer);
	// } catch (LibraryLoaderException e) {
	// // TODO Auto-generated catch block
	// e.printStackTrace();
	// }
	// return commExecutor.execute(state, pid, statement, "$gcomm_create");
	// }
}
