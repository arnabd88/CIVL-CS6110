/**
 * 
 */
package edu.udel.cis.vsl.civl.semantics.common;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.log.IF.CIVLExecutionException;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.Certainty;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.SystemFunction;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression.BINARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.DotExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.InitialValueExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.AssignStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.AssumeStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.CivlForEnterStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.CivlParForEnterStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.MallocStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ReturnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.statement.StatementList;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryLoaderException;
import edu.udel.cis.vsl.civl.semantics.IF.Transition;
import edu.udel.cis.vsl.civl.state.IF.DynamicScope;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.StackEntry;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Triple;
import edu.udel.cis.vsl.gmc.ErrorLog;
import edu.udel.cis.vsl.gmc.GMCConfiguration;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SARLException;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
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

	private int parProcId = 0;

	/* ***************************** Constructors ************************** */

	/**
	 * Create a new executor.
	 * 
	 * @param model
	 *            The model being executed.
	 * @param universe
	 *            A symbolic universe for creating new values.
	 * @param stateFactory
	 *            A state factory. Used by the Executor to create new processes.
	 * @param prover
	 *            A theorem prover for checking assertions.
	 */
	public CommonExecutor(GMCConfiguration config, ModelFactory modelFactory,
			StateFactory stateFactory, ErrorLog log,
			LibraryExecutorLoader loader, Evaluator evaluator,
			CIVLErrorLogger errorLogger, CIVLConfiguration civlConfig) {
		this.civlConfig = civlConfig;
		this.universe = modelFactory.universe();
		this.stateFactory = stateFactory;
		this.modelFactory = modelFactory;
		this.evaluator = evaluator;
		this.loader = loader;
		this.symbolicUtil = evaluator.symbolicUtility();
		this.errorLogger = errorLogger;
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

		state = assign(eval.state, pid, process, statement.getLhs(),
				eval.value, statement.isInitialization());
		state = stateFactory.setLocation(state, pid, statement.target());
		return state;
	}

	/**
	 * TODO javadocs
	 * 
	 * @param state
	 * @param pid
	 * @param statement
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeAssume(State state, int pid, AssumeStatement statement)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluator.evaluate(state, pid,
				statement.getExpression());
		BooleanExpression assumeValue = (BooleanExpression) eval.value;
		BooleanExpression oldPathCondition, newPathCondition;

		state = eval.state;
		oldPathCondition = state.getPathCondition();
		newPathCondition = universe.and(oldPathCondition, assumeValue);
		state = state.setPathCondition(newPathCondition);
		state = stateFactory.setLocation(state, pid, statement.target());
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
			String libraryName = ((SystemFunction) statement.function())
					.getLibrary();

			try {
				LibraryExecutor executor = loader.getLibraryExecutor(
						libraryName, this, this.modelFactory,
						this.symbolicUtil, this.civlConfig);

				state = executor.execute(state, pid, statement);
			} catch (LibraryLoaderException exception) {
				String process = state.getProcessState(pid).name() + "(id="
						+ pid + ")";
				CIVLExecutionException err = new CIVLExecutionException(
						ErrorKind.LIBRARY, Certainty.PROVEABLE, process,
						"An error is encountered when loading the library executor for "
								+ libraryName + ": " + exception.getMessage(),
						this.symbolicUtil.stateToString(state),
						statement.getSource());

				this.errorLogger.reportError(err);
			}
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
			if (function == null) {
				Triple<State, CIVLFunction, Integer> eval = evaluator
						.evaluateFunctionPointer(state, pid,
								statement.functionExpression(),
								statement.getSource());

				function = eval.second;
				state = eval.first;
				state = stateFactory.pushCallStack(state, pid, function,
						eval.third, arguments);
			} else
				state = stateFactory.pushCallStack(state, pid, function,
						arguments);
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
		int sid = state.getProcessState(pid).getDyscopeId();
		int index = statement.getMallocId();
		IntObject indexObj = universe.intObject(index);
		LHSExpression lhs = statement.getLHS();
		Evaluation eval;
		SymbolicExpression scopeValue;
		int dyScopeID;
		DynamicScope dyScope;
		int heapVariableId;
		ReferenceExpression symRef;
		SymbolicExpression heapValue;
		SymbolicExpression heapPointer;
		NumericExpression mallocSize, elementSize;
		BooleanExpression pathCondition, claim;
		ResultType validity;
		NumericExpression elementCount;
		SymbolicExpression heapField;
		NumericExpression lengthExpression;
		int length; // num allocated objects in index component of heap
		StringObject newObjectName;
		SymbolicType newObjectType;
		SymbolicExpression newObject;
		SymbolicExpression firstElementPointer; // returned value

		eval = evaluator.evaluate(state, pid, statement.getScopeExpression());
		state = eval.state;
		scopeValue = eval.value;
		dyScopeID = modelFactory.getScopeId(statement.getScopeExpression()
				.getSource(), scopeValue);
		dyScope = state.getScope(dyScopeID);
		heapVariableId = dyScope.lexicalScope().variable("__heap").vid();
		heapValue = dyScope.getValue(heapVariableId);
		if (heapValue.isNull()) {
			heapValue = symbolicUtil.initialHeapValue();
		}
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
			Certainty certainty = validity == ResultType.NO ? Certainty.PROVEABLE
					: Certainty.MAYBE;
			String elementType = statement.getStaticElementType().toString();
			String message = "For a $malloc returning " + elementType
					+ "*, the size argument must be a multiple of sizeof("
					+ elementType + ")\n" + "      actual size argument: "
					+ mallocSize.toString() + "\n"
					+ "      expected size argument: a multile of "
					+ elementSize.toString();
			CIVLExecutionException e = new CIVLExecutionException(
					ErrorKind.MALLOC, certainty, process, message,
					symbolicUtil.stateToString(state), source);

			errorLogger.reportError(e);
			state = state.setPathCondition(universe.and(pathCondition, claim));
		}
		elementCount = universe.divide(mallocSize, elementSize);
		heapField = universe.tupleRead(heapValue, indexObj);
		lengthExpression = universe.length(heapField);
		length = symbolicUtil.extractInt(source, lengthExpression);
		newObjectName = universe.stringObject("H_p" + pid + "s" + sid + "v"
				+ heapVariableId + "i" + index + "l" + length);
		newObjectType = universe.arrayType(statement.getDynamicElementType(),
				elementCount);
		newObject = universe.symbolicConstant(newObjectName, newObjectType);
		heapField = universe.append(heapField, newObject);
		heapValue = universe.tupleWrite(heapValue, indexObj, heapField);
		state = stateFactory.setVariable(state, heapVariableId, dyScopeID,
				heapValue);
		if (lhs != null) {
			symRef = (ReferenceExpression) universe.canonic(universe
					.identityReference());
			heapPointer = universe.tuple(
					modelFactory.pointerSymbolicType(),
					Arrays.asList(new SymbolicExpression[] {
							modelFactory.scopeValue(dyScopeID),
							universe.integer(heapVariableId), symRef }));
			symRef = universe.tupleComponentReference(symRef, indexObj);
			symRef = universe.arrayElementReference(symRef, lengthExpression);
			symRef = universe.arrayElementReference(symRef, universe.zeroInt());
			firstElementPointer = symbolicUtil.setSymRef(heapPointer, symRef);
			state = assign(state, pid, process, lhs, firstElementPointer);
		}
		state = stateFactory.setLocation(state, pid, statement.target());
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
		String functionName;

		processState = state.getProcessState(pid);
		functionName = processState.peekStack().location().function().name()
				.name();
		if (functionName.equals("_CIVL_system")) {
			DynamicScope rootDyscope = state.getScope(0);
			SymbolicExpression heapValue = rootDyscope.getValue(0);

			assert pid == 0;
			if (!symbolicUtil.isEmptyHeap(heapValue)) {
				CIVLExecutionException err = new CIVLExecutionException(
						ErrorKind.MEMORY_LEAK,
						Certainty.CONCRETE,
						process,
						"The root dyscope d0 (id=0) has a non-empty heap upon termination of the program: "
								+ symbolicUtil.symbolicExpressionToString(
										statement.getSource(), state, heapValue),
						symbolicUtil.stateToString(state), statement
								.getSource());

				this.errorLogger.reportError(err);
			}
			if (state.numProcs() > 1) {
				for (ProcessState proc : state.getProcessStates()) {
					if (proc == null)
						continue;
					if (proc.getPid() == pid)
						continue;
					if (!proc.hasEmptyStack()) {
						CIVLExecutionException err = new CIVLExecutionException(
								ErrorKind.PROCESS_LEAK,
								Certainty.CONCRETE,
								process,
								"Attempt to terminate the main process while process "
										+ proc.identifier() + "(process<"
										+ proc.getPid() + ">) is still running",
								symbolicUtil.stateToString(state), statement
										.getSource());

						this.errorLogger.reportError(err);
					}
				}
			}

		}
		if (expr == null) {
			returnValue = null;
		} else {
			Evaluation eval = evaluator.evaluate(state, pid, expr);

			returnValue = eval.value;
			state = eval.state;
			if (functionName.equals("_CIVL_system")) {
				if (universe.equals(returnValue, universe.integer(0)).isFalse()) {
					CIVLExecutionException err = new CIVLExecutionException(
							ErrorKind.OTHER, Certainty.CONCRETE, process,
							"Program exits with error code: " + returnValue,
							statement.getSource());

					this.errorLogger.reportError(err);
				}
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
					CIVLExecutionException err = new CIVLExecutionException(
							ErrorKind.OTHER,
							Certainty.PROVEABLE,
							process,
							"The lhs "
									+ call.lhs()
									+ " cannot be updated because the invocaion of"
									+ " the function " + functionName
									+ " returns without any expression.",
							symbolicUtil.stateToString(state), call.getSource());

					this.errorLogger.reportError(err);
				}
				state = assign(state, pid, process, call.lhs(), returnValue);
			}
			state = stateFactory.setLocation(state, pid, call.target());
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

		assert !statement.isCall();
		for (int i = 0; i < numArgs; i++) {
			Evaluation eval = evaluator.evaluate(state, pid,
					argumentExpressions.get(i));

			state = eval.state;
			arguments[i] = eval.value;
		}
		if (function == null) {
			Triple<State, CIVLFunction, Integer> eval = evaluator
					.evaluateFunctionPointer(state, pid,
							statement.functionExpression(),
							statement.getSource());

			state = eval.first;
			function = eval.second;
			state = stateFactory.addProcess(state, function, eval.third,
					arguments, pid);
		} else
			state = stateFactory.addProcess(state, function, arguments, pid);
		if (statement.lhs() != null)
			state = assign(state, pid, process, statement.lhs(),
					modelFactory.processValue(newPid));
		state = stateFactory.setLocation(state, pid, statement.target());
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
			return executeWork(state, pid, statement);
		} catch (SARLException e) {
			// e.printStackTrace(System.err);
			// System.err.flush();
			throw new CIVLInternalException("SARL exception: " + e, statement);
		} catch (CIVLExecutionException e) {
			errorLogger.reportError(e);
			throw new UnsatisfiablePathConditionException();
		}
	}

	private State executeStatementList(State state, int pid,
			StatementList statement, SymbolicExpression value)
			throws UnsatisfiablePathConditionException {
		int count = statement.statements().size();

		for (int i = 0; i < count; i++) {
			Statement stmt = statement.statements().get(i);

			state = executeWork(state, pid, stmt);
		}
		return state;
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

		numSteps++;
		switch (statement.statementKind()) {
		case ASSIGN:
			return executeAssign(state, pid, process,
					(AssignStatement) statement);
		case ASSUME:
			return executeAssume(state, pid, (AssumeStatement) statement);
		case CALL_OR_SPAWN:
			CallOrSpawnStatement call = (CallOrSpawnStatement) statement;

			if (call.isCall())
				return executeCall(state, pid, call);
			else
				return executeSpawn(state, pid, process, call);
		case CHOOSE:
			throw new CIVLInternalException("Should be unreachable", statement);
		case MALLOC:
			return executeMalloc(state, pid, process,
					(MallocStatement) statement);
		case NOOP:
			return stateFactory.setLocation(state, pid, statement.target());
		case RETURN:
			return executeReturn(state, pid, process,
					(ReturnStatement) statement);
		case STATEMENT_LIST:
			return executeStatementList(state, pid, (StatementList) statement,
					null);
		case CIVL_FOR_ENTER:
			return executeCivlFor(state, pid, (CivlForEnterStatement) statement);
		case CIVL_PAR_FOR_ENTER:
			return executeCivlParFor(state, pid,
					(CivlParForEnterStatement) statement);
		default:
			throw new CIVLInternalException("Unknown statement kind", statement);
		}
	}

	private State executeCivlParFor(State state, int pid,
			CivlParForEnterStatement parFor)
			throws UnsatisfiablePathConditionException {
		CIVLSource source = parFor.getSource();
		Expression domain = parFor.domain();
		VariableExpression domSize = parFor.domSizeVar();
		Evaluation eval;
		SymbolicExpression domainV;
		NumericExpression domSizeV = universe.integer(1);
		int dim = parFor.dimension();
		String process = state.getProcessState(pid).name() + "(id=" + pid + ")";
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		IntegerNumber number_domSize;
		List<NumericExpression> lows = new ArrayList<>(dim);
		List<NumericExpression> steps = new ArrayList<>(dim);
		List<NumericExpression> highs = new ArrayList<>(dim);
		Expression parProcs = parFor.parProcsPointer();
		VariableExpression parProcsVar = parFor.parProcsVar();
		SymbolicExpression parProcsPointer;

		eval = evaluator.evaluate(state, pid, domain);
		domainV = eval.value;
		state = eval.state;
		eval = evaluator.evaluate(state, pid, parProcs);
		state = eval.state;
		for (int i = 0; i < dim; i++) {
			SymbolicExpression rangeV = universe.tupleRead(domainV,
					universe.intObject(i));
			NumericExpression rangeSize = symbolicUtil.getRangeSize(rangeV);

			domSizeV = universe.multiply(domSizeV, rangeSize);
			lows.add(symbolicUtil.getLowOfRange(rangeV));
			steps.add(symbolicUtil.getStepOfRange(rangeV));
			highs.add(symbolicUtil.getHighOfRange(rangeV));
		}
		state = this.assign(state, pid, process, domSize, domSizeV);
		number_domSize = (IntegerNumber) reasoner.extractNumber(domSizeV);
		if (number_domSize == null) {
			CIVLExecutionException err = new CIVLExecutionException(
					ErrorKind.OTHER, Certainty.PROVEABLE, process,
					"The arguments of the domain for $parfor "
							+ "must be concrete.",
					symbolicUtil.stateToString(state), source);

			this.errorLogger.reportError(err);
		} else {
			InitialValueExpression initVal = modelFactory
					.initialValueExpression(parProcs.getSource(),
							parProcsVar.variable());

			eval = evaluator.evaluate(state, pid, parProcs);
			parProcsPointer = eval.value;
			state = eval.state;
			eval = evaluator.evaluate(state, pid, initVal);
			state = eval.state;
			state = this.assign(state, pid, process, parProcsVar, eval.value);
			this.parProcId = 0;
			state = this.executeSpawns(state, pid, parProcs, parProcsPointer,
					parFor.parProcFunction(), 0, dim, lows, steps, highs);
			this.parProcId = 0;
		}
		state = stateFactory.setLocation(state, pid, parFor.target());
		return state;
	}

	private State executeSpawns(State state, int pid, Expression parProcs,
			SymbolicExpression parProcsPointer, CIVLFunction function, int id,
			int dim, List<NumericExpression> values,
			List<NumericExpression> steps, List<NumericExpression> highs)
			throws UnsatisfiablePathConditionException {
		NumericExpression current = values.get(id);
		NumericExpression step = steps.get(id), high = highs.get(id);
		Reasoner reasoner;
		BooleanExpression claim;
		ResultType result;
		String process = state.getProcessState(pid).name() + "(id=" + pid + ")";
		List<NumericExpression> myValues = new ArrayList<>(values);

		for (int i = 0;; i++) {
			if (i != 0)
				current = universe.add(current, step);
			reasoner = universe.reasoner(state.getPathCondition());
			claim = universe.lessThanEquals(current, high);
			result = reasoner.valid(claim).getResultType();

			if (result == ResultType.YES) {
				myValues.set(id, current);
				if (id == dim - 1) {
					SymbolicExpression[] arguments = new SymbolicExpression[dim];
					SymbolicExpression procPointer;
					int myProcId = this.parProcId++;
					int newPid;
					CIVLSource source = parProcs.getSource();
					BinaryExpression pointerAdd = modelFactory
							.binaryExpression(source,
									BINARY_OPERATOR.POINTER_ADD, parProcs,
									modelFactory.integerLiteralExpression(
											source,
											BigInteger.valueOf(myProcId)));
					Evaluation eval;

					myValues.toArray(arguments);
					newPid = state.numProcs();
					state = stateFactory.addProcess(state, function, arguments,
							pid);
					eval = evaluator.pointerAdd(state, pid, process,
							pointerAdd, parProcsPointer,
							universe.integer(myProcId));
					procPointer = eval.value;
					state = eval.state;
					state = this.assign(source, state, process, procPointer,
							modelFactory.processValue(newPid));
				} else {
					state = executeSpawns(state, pid, parProcs,
							parProcsPointer, function, id + 1, dim, myValues,
							steps, highs);
				}
			} else if (result == ResultType.NO)
				break;
			else {

			}

		}
		return state;
	}

	private State executeCivlFor(State state, int pid,
			CivlForEnterStatement forEnter)
			throws UnsatisfiablePathConditionException {
		List<VariableExpression> loopVars = forEnter.loopVariables();
		Expression domain = forEnter.domain();
		SymbolicExpression domValue;
		Evaluation eval = evaluator.evaluate(state, pid, domain);
		int dim = loopVars.size();
		String process = state.getProcessState(pid).name() + "(id=" + pid + ")";

		domValue = eval.value;
		state = eval.state;
		for (int i = dim - 1; i >= 0; i--) {
			VariableExpression var = loopVars.get(i);
			SymbolicExpression varValue, newValue;
			BooleanExpression inRange;

			eval = evaluator.evaluate(state, pid, var);
			varValue = eval.value;
			state = eval.state;
			newValue = symbolicUtil.rangeIncremental(varValue,
					symbolicUtil.rangeOfDomainAt(domValue, i));
			inRange = symbolicUtil.isInRange(newValue, domValue, i);
			if (!inRange.isFalse()) {
				state = this.assign(state, pid, process, var, newValue);
				break;
			} else if (i == 0) {
				state = this.assign(state, pid, process, var, newValue);
			} else {
				state = this.assign(state, pid, process, var,
						symbolicUtil.getLowOfDomainAt(domValue, i));
			}
		}
		state = stateFactory.setLocation(state, pid, forEnter.target());
		return state;
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
		int vid = symbolicUtil.getVariableId(source, pointer);
		int sid = symbolicUtil.getDyscopeId(source, pointer);
		ReferenceExpression symRef = symbolicUtil.getSymRef(pointer);
		State result;
		Variable variable;
		Evaluation eval;

		eval = evaluator.dereference(source, state, process, pointer, false);
		state = eval.state;
		if (symbolicUtil.isUndefinedConstant(eval.value)) {
			errorLogger.logSimpleError(source, state, process,
					symbolicUtil.stateToString(state), ErrorKind.DEREFERENCE,
					"Attempt to dereference a pointer that refers to a "
							+ "memory space that is already deallocated");
			throw new UnsatisfiablePathConditionException();
		}
		if (sid < 0) {
			errorLogger
					.logSimpleError(source, state, process,
							symbolicUtil.stateToString(state),
							ErrorKind.DEREFERENCE,
							"Attempt to dereference pointer into scope which has been removed from state");
			throw new UnsatisfiablePathConditionException();
		}
		variable = state.getScope(sid).lexicalScope().variable(vid);
		if (!isInitialization) {
			if (variable.isInput()) {
				errorLogger
						.logSimpleError(source, state, process,
								symbolicUtil.stateToString(state),
								ErrorKind.INPUT_WRITE,
								"Attempt to write to input variable "
										+ variable.name());
				throw new UnsatisfiablePathConditionException();
			} else if (variable.isConst()) {
				errorLogger.logSimpleError(
						source,
						state,
						process,
						symbolicUtil.stateToString(state),
						ErrorKind.CONSTANT_WRITE,
						"Attempt to write to constant variable "
								+ variable.name());
				throw new UnsatisfiablePathConditionException();
			}
		}
		// eval = evaluator.dereference(source, state, process, pointer, false);
		// state = eval.state;
		// if (!symbolicUtil.isHeapObjectDefined(eval.value)) {
		// errorLogger.logSimpleError(source, state, process,
		// symbolicUtil.stateToString(state), ErrorKind.MEMORY_LEAK,
		// "Attempt to write to an undefined memory space");
		// throw new UnsatisfiablePathConditionException();
		// }
		if (symRef.isIdentityReference()) {
			result = stateFactory.setVariable(state, vid, sid, value);
		} else {
			SymbolicExpression oldVariableValue = state.getVariableValue(sid,
					vid);

			try {
				SymbolicExpression newVariableValue = universe.assign(
						oldVariableValue, symRef, value);

				result = stateFactory.setVariable(state, vid, sid,
						newVariableValue);
			} catch (SARLException e) {
				errorLogger.logSimpleError(
						source,
						state,
						process,
						symbolicUtil.stateToString(state),
						ErrorKind.DEREFERENCE,
						"Invalid pointer dereference: "
								+ symbolicUtil.symbolicExpressionToString(
										source, state, pointer));
				throw new UnsatisfiablePathConditionException();
			}
		}
		return result;
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
		int index = modelFactory.getHeapFieldId(objectType);
		IntObject indexObj = universe.intObject(index);
		int dyScopeID;
		DynamicScope dyScope;
		int heapVariableId;
		ReferenceExpression symRef;
		SymbolicExpression heapValue;
		SymbolicExpression heapPointer;
		SymbolicExpression heapField;
		SymbolicExpression newObject;
		NumericExpression fieldLength;
		SymbolicExpression firstElementPointer; // returned value
		ArrayList<SymbolicExpression> elements = new ArrayList<>();
		CIVLSource scopeSource = scopeExpression == null ? null
				: scopeExpression.getSource();

		elements.add(objectValue);
		heapValue = evaluator.heapValue(source, state, process, scopeValue);
		dyScopeID = modelFactory.getScopeId(scopeSource, scopeValue);
		dyScope = state.getScope(dyScopeID);
		heapVariableId = dyScope.lexicalScope().variable("__heap").vid();
		heapField = universe.tupleRead(heapValue, indexObj);
		fieldLength = universe.length(heapField);
		newObject = universe.array(objectType.getDynamicType(universe),
				elements);
		heapField = universe.append(heapField, newObject);
		heapValue = universe.tupleWrite(heapValue, indexObj, heapField);
		state = stateFactory.setVariable(state, heapVariableId, dyScopeID,
				heapValue);
		if (lhs != null) {
			symRef = (ReferenceExpression) universe.canonic(universe
					.identityReference());
			heapPointer = universe.tuple(
					modelFactory.pointerSymbolicType(),
					Arrays.asList(new SymbolicExpression[] {
							modelFactory.scopeValue(dyScopeID),
							universe.integer(heapVariableId), symRef }));
			symRef = universe.tupleComponentReference(symRef, indexObj);
			symRef = universe.arrayElementReference(symRef, fieldLength);
			symRef = universe.arrayElementReference(symRef, universe.zeroInt());
			firstElementPointer = symbolicUtil.setSymRef(heapPointer, symRef);
			state = assign(state, pid, process, lhs, firstElementPointer);
		}
		return state;
	}

	@Override
	public StateFactory stateFactory() {
		return stateFactory;
	}

	@Override
	public State execute(State state, int pid, Transition transition)
			throws UnsatisfiablePathConditionException {
		state = state.setPathCondition(transition.pathCondition());
		return this.executeStatement(state, pid, transition.statement());
	}

	@Override
	public CIVLErrorLogger errorLogger() {
		return this.errorLogger;
	}
}
