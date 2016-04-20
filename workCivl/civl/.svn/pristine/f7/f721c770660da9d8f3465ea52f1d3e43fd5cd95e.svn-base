/**
 * 
 */
package edu.udel.cis.vsl.civl.semantics;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import edu.udel.cis.vsl.civl.err.CIVLExecutionException;
import edu.udel.cis.vsl.civl.err.CIVLExecutionException.Certainty;
import edu.udel.cis.vsl.civl.err.CIVLExecutionException.ErrorKind;
import edu.udel.cis.vsl.civl.err.CIVLInternalException;
import edu.udel.cis.vsl.civl.err.CIVLStateException;
import edu.udel.cis.vsl.civl.err.CIVLSyntaxException;
import edu.udel.cis.vsl.civl.err.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.err.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.kripke.Enabler;
import edu.udel.cis.vsl.civl.library.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.library.IF.LibraryLoader;
import edu.udel.cis.vsl.civl.library.civlc.LibcivlcExecutor;
import edu.udel.cis.vsl.civl.library.stdio.LibstdioExecutor;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.SystemFunction;
import edu.udel.cis.vsl.civl.model.IF.expression.DotExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.AssertStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.AssignStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.AssumeStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ChooseStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.MallocStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ReturnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.statement.WaitStatement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPointerType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.model.common.statement.StatementList;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.state.IF.DynamicScope;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.StackEntry;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.util.Pair;
import edu.udel.cis.vsl.gmc.ErrorLog;
import edu.udel.cis.vsl.gmc.GMCConfiguration;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SARLException;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.ValidityResult;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.ArrayElementReference;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicUnionType;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicSequence;

/**
 * An executor is used to execute a CIVL statement. The basic method provided
 * takes a state and a statement, and modifies the state according to the
 * semantics of that statement.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonExecutor implements Executor {

	/* ******************************* Types ******************************* */

	/**
	 * The status of the execution of a statement.
	 * 
	 * <ol>
	 * <li>NORMAL: normal execution;</li>
	 * <li>NONDETERMINISTIC: nondeterminism exists in the statement;</li>
	 * <li>BLOCKED: the statement is blocked.</li>
	 * </ol>
	 * 
	 * @author Manchun Zheng (zmanchun)
	 */
	public enum StateStatusKind {
		NORMAL, NONDETERMINISTIC, BLOCKED
	}

	/* *************************** Instance Fields ************************* */

	/**
	 * The unique library executor for civlc.h.
	 */
	protected LibcivlcExecutor civlcExecutor;

	/**
	 * Enable or disable printing. True by default.
	 */
	protected boolean enablePrintf;

	/**
	 * The unique enabler used in the system. Used in this class to evaluate the
	 * guard of a statement.
	 */
	protected Enabler enabler;

	/** The Evaluator used to evaluate expressions. */
	protected Evaluator evaluator;

	/**
	 * The loader used to find Executors for system functions declared in
	 * libraries.
	 */
	protected LibraryLoader loader;

	/**
	 * The unique model factory used in the system.
	 */
	protected ModelFactory modelFactory;

	/**
	 * The number of steps that have been executed by this executor. A "step" is
	 * defined to be a call to method
	 * {@link #executeWork(State, int, Statement)}.
	 */
	protected long numSteps = 0;

	/**
	 * The printing stream to be used.
	 */
	protected PrintStream output;

	/** The factory used to produce and manipulate model states. */
	protected StateFactory stateFactory;

	/**
	 * The unique library executor for stdio.h.
	 */
	protected LibstdioExecutor stdioExecutor;

	/** The symbolic universe used to manage all symbolic expressions. */
	protected SymbolicUniverse universe;

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
			StateFactory stateFactory, ErrorLog log, LibraryLoader loader,
			PrintStream output, boolean enablePrintf, Evaluator evaluator) {
		this.universe = modelFactory.universe();
		this.stateFactory = stateFactory;
		this.modelFactory = modelFactory;
		this.evaluator = evaluator;
		this.loader = loader;
		this.output = output;
		this.enablePrintf = enablePrintf;
		this.civlcExecutor = (LibcivlcExecutor) loader.getLibraryExecutor(
				"civlc", this, this.output, this.enablePrintf,
				this.modelFactory);
	}

	/**
	 * Create a new executor with null library loader.
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
			StateFactory stateFactory, ErrorLog log, PrintStream output,
			boolean enablePrintf, Evaluator evaluator) {
		this(config, modelFactory, stateFactory, log, null, output,
				enablePrintf, evaluator);
	}

	/* ************************** Private methods ************************** */

	/**
	 * TODO javadocs
	 * 
	 * @param state
	 * @param pid
	 * @param statement
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeAssert(State state, int pid, AssertStatement statement)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluator.evaluate(state, pid,
				statement.getExpression());
		BooleanExpression assertValue = (BooleanExpression) eval.value;
		Reasoner reasoner;
		ValidityResult valid;
		ResultType resultType;

		state = eval.state;
		reasoner = universe.reasoner(state.getPathCondition());
		valid = reasoner.valid(assertValue);
		resultType = valid.getResultType();
		if (resultType != ResultType.YES) {
			if (statement.printfArguments() != null) {
				if (!this.enablePrintf) {
					return state;
				} else {
					// obtain printf() arguments
					Expression[] arguments = statement.printfArguments();
					SymbolicExpression[] argumentValues = new SymbolicExpression[arguments.length];
					for (int i = 0; i < arguments.length; i++) {

						eval = evaluator.evaluate(state, pid, arguments[i]);
						state = eval.state;
						argumentValues[i] = eval.value;
					}
					state = this.executePrintf(state, pid, arguments,
							argumentValues);
				}
			}
			// TODO: USE GENERAL METHOD ... state = evaluator.logError in own
			// class
			state = evaluator.logError(statement.getSource(), state,
					assertValue, resultType, ErrorKind.ASSERTION_VIOLATION,
					"Cannot prove assertion holds: " + statement.toString()
							+ "\n  Path condition: " + state.getPathCondition()
							+ "\n  Assertion: " + assertValue + "\n");
		}
		state = stateFactory.setLocation(state, pid, statement.target());
		return state;
	}

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
	private State executeAssign(State state, int pid, AssignStatement statement)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluator.evaluate(state, pid, statement.rhs());

		state = assign(eval.state, pid, statement.getLhs(), eval.value,
				statement.isInitialization());
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
			// TODO: optimize this. store libraryExecutor in SystemFunction?
			LibraryExecutor executor = loader.getLibraryExecutor(
					((SystemFunction) statement.function()).getLibrary(), this,
					output, this.enablePrintf, this.modelFactory);

			state = executor.execute(state, pid, statement);
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
				Pair<State, CIVLFunction> eval = evaluator
						.evaluateFunctionExpression(state, pid,
								statement.functionExpression());

				function = eval.right;
				state = eval.left;
			}
			state = stateFactory.pushCallStack(state, pid, function, arguments);
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
	private State executeMalloc(State state, int pid, MallocStatement statement)
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
		if (heapValue.equals(universe.nullExpression())) {
			heapValue = evaluator.initialHeapValue();
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
			CIVLStateException e = new CIVLStateException(ErrorKind.MALLOC,
					certainty,
					"Size argument to $malloc is not multiple of element size",
					eval.state, this.stateFactory, source);

			evaluator.reportError(e);
			state = state.setPathCondition(universe.and(pathCondition, claim));
		}
		elementCount = universe.divide(mallocSize, elementSize);
		heapField = universe.tupleRead(heapValue, indexObj);
		lengthExpression = universe.length(heapField);
		length = evaluator.extractInt(source, lengthExpression);
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
			firstElementPointer = evaluator.setSymRef(heapPointer, symRef);
			state = assign(state, pid, lhs, firstElementPointer);
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
	private State executeReturn(State state, int pid, ReturnStatement statement)
			throws UnsatisfiablePathConditionException {
		Expression expr = statement.expression();
		ProcessState process;
		SymbolicExpression returnValue;
		String functionName;

		process = state.getProcessState(pid);
		functionName = process.peekStack().location().function().name().name();
		if (functionName.equals("_CIVL_system")) {
			assert pid == 0;
			if (state.numProcs() > 1) {
				for (ProcessState proc : state.getProcessStates()) {
					if (proc == null)
						continue;
					if (proc.getPid() == pid)
						continue;
					if (!proc.hasEmptyStack()) {
						throw new CIVLExecutionException(
								ErrorKind.PROCESS_LEAK, Certainty.CONCRETE,
								"Attempt to terminate the main process while process "
										+ proc.identifier() + "(process<"
										+ proc.getPid()
										+ ">) is still running.",
								statement.getSource());
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
		}
		state = stateFactory.popCallStack(state, pid);
		process = state.getProcessState(pid);
		if (!process.hasEmptyStack()) {
			StackEntry returnContext = process.peekStack();
			Location returnLocation = returnContext.location();
			CallOrSpawnStatement call = (CallOrSpawnStatement) returnLocation
					.getSoleOutgoing();

			if (call.lhs() != null)
				state = assign(state, pid, call.lhs(), returnValue);
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
	private State executeSpawn(State state, int pid,
			CallOrSpawnStatement statement)
			throws UnsatisfiablePathConditionException {
		CIVLFunction function = statement.function();
		int newPid = state.numProcs();
		List<Expression> argumentExpressions = statement.arguments();
		int numArgs = argumentExpressions.size();
		SymbolicExpression[] arguments = new SymbolicExpression[numArgs];

		assert !statement.isCall();
		if (function == null) {
			Pair<State, CIVLFunction> eval = evaluator
					.evaluateFunctionExpression(state, pid,
							statement.functionExpression());

			state = eval.left;
			function = eval.right;
		}
		for (int i = 0; i < numArgs; i++) {
			Evaluation eval = evaluator.evaluate(state, pid,
					argumentExpressions.get(i));

			state = eval.state;
			arguments[i] = eval.value;
		}
		state = stateFactory.addProcess(state, function, arguments, pid);
		if (statement.lhs() != null)
			state = assign(state, pid, statement.lhs(),
					modelFactory.processValue(newPid));
		state = stateFactory.setLocation(state, pid, statement.target());
		return state;
	}

	/**
	 * Execute a join statement. The state will be updated to no longer have the
	 * joined process.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The process id of the currently executing process.
	 * @param statement
	 *            The join statement to be executed.
	 * @return The updated state of the program.
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeWait(State state, int pid, WaitStatement statement)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluator.evaluate(state, pid, statement.process());
		SymbolicExpression procVal = eval.value;
		int joinedPid = modelFactory.getProcessId(statement.process()
				.getSource(), procVal);

		state = stateFactory.setLocation(eval.state, pid, statement.target());
		state = stateFactory.removeProcess(state, joinedPid);
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
		numSteps++;

		switch (statement.statementKind()) {
		case ASSERT:
			return executeAssert(state, pid, (AssertStatement) statement);
		case ASSIGN:
			return executeAssign(state, pid, (AssignStatement) statement);
		case ASSUME:
			return executeAssume(state, pid, (AssumeStatement) statement);
		case CALL_OR_SPAWN:
			CallOrSpawnStatement call = (CallOrSpawnStatement) statement;

			if (call.isCall())
				return executeCall(state, pid, call);
			else
				return executeSpawn(state, pid, call);
		case CHOOSE:
			throw new CIVLInternalException("Should be unreachable", statement);
		case MALLOC:
			return executeMalloc(state, pid, (MallocStatement) statement);
		case NOOP:
			return stateFactory.setLocation(state, pid, statement.target());
		case RETURN:
			return executeReturn(state, pid, (ReturnStatement) statement);
		case STATEMENT_LIST:
			return executeStatementList(state, pid, (StatementList) statement,
					null);
		case WAIT:
			return executeWait(state, pid, (WaitStatement) statement);
		default:
			throw new CIVLInternalException("Unknown statement kind", statement);
		}
	}

	/**
	 * TODO javadocs
	 * 
	 * @param source
	 * @param library
	 * @return
	 */
	@Override
	public LibraryExecutor libraryExecutor(CIVLSource source, String library) {
		switch (library) {
		case "civlc":
			return civlcExecutor;
		case "stdio":
			if (stdioExecutor == null)
				this.stdioExecutor = (LibstdioExecutor) loader
						.getLibraryExecutor("stdio", this, this.output,
								this.enablePrintf, this.modelFactory);
			return stdioExecutor;
		default:
			throw new CIVLInternalException("Unknown library: " + library,
					source);
		}
	}

	/* ********************* Methods from Executor ************************* */

	@Override
	public State assign(CIVLSource source, State state,
			SymbolicExpression pointer, SymbolicExpression value)
			throws UnsatisfiablePathConditionException {
		return this.assign(source, state, pointer, value, false);
	}

	private State assign(CIVLSource source, State state,
			SymbolicExpression pointer, SymbolicExpression value,
			boolean isInitialization)
			throws UnsatisfiablePathConditionException {
		int vid = evaluator.getVariableId(source, pointer);
		int sid = evaluator.getScopeId(source, pointer);
		ReferenceExpression symRef = evaluator.getSymRef(pointer);
		State result;
		Variable variable;

		if (sid < 0) {
			evaluator
					.logSimpleError(source, state, ErrorKind.DEREFERENCE,
							"Attempt to dereference pointer into scope which has been removed from state");
			throw new UnsatisfiablePathConditionException();
		}
		variable = state.getScope(sid).lexicalScope().variable(vid);
		if (!isInitialization) {
			if (variable.isInput()) {
				evaluator
						.logSimpleError(source, state, ErrorKind.INPUT_WRITE,
								"Attempt to write to input variable "
										+ variable.name());
				throw new UnsatisfiablePathConditionException();
			} else if (variable.isConst()) {
				evaluator.logSimpleError(
						source,
						state,
						ErrorKind.CONSTANT_WRITE,
						"Attempt to write to constant variable "
								+ variable.name());
				throw new UnsatisfiablePathConditionException();
			}
		}
		if (symRef.isIdentityReference()) {
			result = stateFactory.setVariable(state, vid, sid, value);
		} else {
			SymbolicExpression oldVariableValue = state.getVariableValue(sid,
					vid);
			SymbolicExpression newVariableValue = universe.assign(
					oldVariableValue, symRef, value);

			result = stateFactory
					.setVariable(state, vid, sid, newVariableValue);
		}
		return result;
	}

	@Override
	public State assign(State state, int pid, LHSExpression lhs,
			SymbolicExpression value)
			throws UnsatisfiablePathConditionException {
		return this.assign(state, pid, lhs, value, false);
	}

	private State assign(State state, int pid, LHSExpression lhs,
			SymbolicExpression value, boolean isInitialization)
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
		return assign(lhs.getSource(), eval.state, eval.value, value,
				isInitialization);
	}

	@Override
	public Enabler enabler() {
		return this.enabler;
	}

	// @Override
	// public Evaluation evaluateSystemGuard(State state, int pid,
	// SystemGuardExpression systemGuard) {
	// LibraryExecutor libExecutor = libraryExecutor(systemGuard.getSource(),
	// systemGuard.library());
	//
	// return libExecutor.getGuard(state, pid, systemGuard.functionName(),
	// systemGuard.arguments(), systemGuard.getSource());
	// }

	@Override
	public Evaluator evaluator() {
		return evaluator;
	}

	@Override
	public State execute(State state, int pid, Statement statement)
			throws UnsatisfiablePathConditionException {
		try {
			return executeWork(state, pid, statement);
		} catch (SARLException e) {
			// e.printStackTrace(System.err);
			// System.err.flush();
			throw new CIVLInternalException("SARL exception: " + e, statement);
		} catch (CIVLExecutionException e) {
			evaluator.reportError(e);
			throw new UnsatisfiablePathConditionException();
		}
	}

	@Override
	public State executeChoose(State state, int pid, ChooseStatement statement,
			SymbolicExpression value)
			throws UnsatisfiablePathConditionException {
		state = assign(state, pid, statement.getLhs(), value);
		state = stateFactory.setLocation(state, pid, statement.target());
		return state;
	}

	@Override
	public Pair<StateStatusKind, State> executeStatement(State state,
			Location location, Statement s, int pid) {
		State newState = null;
		BooleanExpression pathCondition = enabler.newPathCondition(state, pid,
				s);

		if (!pathCondition.isFalse()) {
			try {
				if (s instanceof ChooseStatement) {
					// execute deterministic choose statement
					return new Pair<>(StateStatusKind.NONDETERMINISTIC, state);
				} else if (s instanceof WaitStatement) {
					Evaluation eval = evaluator.evaluate(
							state.setPathCondition(pathCondition), pid,
							((WaitStatement) s).process());
					int pidValue = modelFactory.getProcessId(
							((WaitStatement) s).process().getSource(),
							eval.value);

					if (pidValue < 0) {
						CIVLExecutionException e = new CIVLStateException(
								ErrorKind.INVALID_PID,
								Certainty.PROVEABLE,
								"Unable to call $wait on a process that has already been the target of a $wait.",
								state, this.stateFactory, s.getSource());

						evaluator.reportError(e);
						throw new UnsatisfiablePathConditionException();
					}
					if (state.getProcessState(pidValue).hasEmptyStack()) {
						newState = state.setPathCondition(pathCondition);
						newState = execute(newState, pid, s);
					} else {
						return new Pair<>(StateStatusKind.BLOCKED, state);
					}
				} else {
					newState = state.setPathCondition(pathCondition);
					newState = execute(newState, pid, s);
				}
			} catch (UnsatisfiablePathConditionException e) {
				return new Pair<>(StateStatusKind.BLOCKED, state);
			}
		} else {
			return new Pair<>(StateStatusKind.BLOCKED, state);
		}
		return new Pair<>(StateStatusKind.NORMAL, newState);
	}

	@Override
	public State executeStatementList(State state, int pid,
			StatementList statement, SymbolicExpression value)
			throws UnsatisfiablePathConditionException {
		int count = statement.statements().size();

		for (int i = 0; i < count; i++) {
			Statement stmt = statement.statements().get(i);

			if (stmt instanceof ChooseStatement) {
				state = executeChoose(state, pid, (ChooseStatement) stmt, value);
			} else {
				state = executeWork(state, pid, stmt);
			}
		}
		return state;
	}

	@Override
	public long getNumSteps() {
		return numSteps;
	}

	@Override
	public ModelFactory modelFactory() {
		return modelFactory;
	}

	@Override
	public State malloc(CIVLSource source, State state, int pid,
			LHSExpression lhs, Expression scopeExpression,
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
		heapValue = evaluator.heapValue(source, state, scopeValue);
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
			firstElementPointer = evaluator.setSymRef(heapPointer, symRef);
			state = assign(state, pid, lhs, firstElementPointer);
		}
		return state;
	}

	// (State state, int pid, MallocStatement statement)

	@Override
	public void setEnabler(Enabler enabler) {
		this.enabler = enabler;
	}

	@Override
	public StateFactory stateFactory() {
		return stateFactory;
	}

	@Override
	public SymbolicUniverse universe() {
		return universe;
	}

	@Override
	public State executePrintf(State state, int pid, Expression[] expressions,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		if (this.enablePrintf) {
			// using StringBuffer instead for performance
			StringBuffer stringOfSymbolicExpression = new StringBuffer();
			StringBuffer formatBuffer = new StringBuffer();
			String format;
			ArrayList<String> arguments = new ArrayList<String>();
			CIVLSource source = state.getProcessState(pid).getLocation()
					.getSource();
			// variables used for checking %s
			ArrayList<Integer> sIndexes = new ArrayList<Integer>();
			Pattern pattern;
			Matcher matcher;
			int sCount = 1;

			// don't assume argumentValues[0] is a pointer to an element of an
			// array. Check it. If it is not, through an exception.
			SymbolicExpression arrayPointer = evaluator.parentPointer(source,
					argumentValues[0]);
			Evaluation eval = evaluator
					.dereference(source, state, arrayPointer);

			if (eval.value.operator() != SymbolicOperator.CONCRETE)
				throw new CIVLUnimplementedFeatureException(
						"non-concrete format strings",
						expressions[0].getSource());

			SymbolicSequence<?> originalArray = (SymbolicSequence<?>) eval.value
					.argument(0);

			state = eval.state;

			int numChars = originalArray.size();
			char[] formatChars = new char[numChars];

			for (int i = 0; i < originalArray.size(); i++) {
				SymbolicExpression charExpr = originalArray.get(i);
				Character theChar = universe.extractCharacter(charExpr);

				if (theChar == null)
					throw new CIVLUnimplementedFeatureException(
							"non-concrete character in format string at position "
									+ i, expressions[0].getSource());

				formatChars[i] = theChar;
			}
			formatBuffer.append(formatChars);
			// checking %s: find out all the corresponding argument positions
			// for all %s existed in format string.
			pattern = Pattern
					.compile("((?<=[^%])|^)%[0-9]*[.]?[0-9|*]*[sdfoxegacpuxADEFGX]");
			matcher = pattern.matcher(formatBuffer);
			while (matcher.find()) {
				String formatSpecifier = matcher.group();
				if (formatSpecifier.compareTo("%s") == 0) {
					sIndexes.add(sCount);
				}
				sCount++;
			}
			// format = formatBuffer.toString();
			// splitedFormats = format.split("%s");
			// for (int k = 0; k < splitedFormats.length - 1; k++) {
			// int splitedFormatsLength;
			//
			// splitedFormatsLength = splitedFormats[k]
			// .split("((?<=[^%])|^)%[0-9]*[.]?[0-9|*]*[dfoxegacpuxADEFGX]").length;
			// //is it true? string.split("REX").length == 0 ==> string is fully
			// matched with "REX".
			// if (splitedFormatsLength == 0)
			// splitedFormatsLength = 2;
			// sCount += splitedFormatsLength;
			// sIndexes.add(sCount);
			// }
			for (int i = 1; i < argumentValues.length; i++) {
				SymbolicExpression argument = argumentValues[i];
				CIVLType argumentType = expressions[i].getExpressionType();
				ReferenceExpression ref;
				ArrayElementReference arrayRef;
				NumericExpression arrayIndex;
				int int_arrayIndex;

				if (argumentType instanceof CIVLPointerType
						&& ((CIVLPointerType) argumentType).baseType()
								.isCharType()
						&& argument.operator() == SymbolicOperator.CONCRETE) {
					// also check format code is %s before doing this
					if (!sIndexes.contains(i)) {
						throw new CIVLSyntaxException(
								"Array pointer unaccepted",
								expressions[i].getSource());
					}
					arrayPointer = evaluator.parentPointer(source, argument);
					ref = evaluator.getSymRef(argument);
					assert (ref.isArrayElementReference());
					arrayRef = (ArrayElementReference) evaluator
							.getSymRef(argument);
					arrayIndex = arrayRef.getIndex();
					// what if the index is symbolic ?
					int_arrayIndex = evaluator.extractInt(source, arrayIndex);
					// index is not necessarily 0! FIX ME!
					eval = evaluator.dereference(source, state, arrayPointer);
					originalArray = (SymbolicSequence<?>) eval.value
							.argument(0);
					state = eval.state;
					for (int j = int_arrayIndex; j < originalArray.size(); j++) {
						stringOfSymbolicExpression.append(originalArray.get(j)
								.toString().charAt(1));
					}
					arguments.add(stringOfSymbolicExpression.substring(0));
					// clear stringOfSymbolicExpression
					stringOfSymbolicExpression.delete(0,
							stringOfSymbolicExpression.length());
				} else
					arguments.add(argument.toString());
			}

			// TODO: print pointers in a much nicer way

			// TODO: at model building time, check statically that the
			// expression types are compatible with corresponding conversion
			// specifiers
			format = formatBuffer.substring(0);
			format = format.replaceAll("%lf", "%s");
			format = format
					.replaceAll(
							"((?<=[^%])|^)%[0-9]*[.]?[0-9|*]*[dfoxegacpuxADEFGX]",
							"%s");
			for (int i = 0; i < format.length(); i++) {
				if (format.charAt(i) == '%') {
					if (format.charAt(i + 1) == '%') {
						i++;
						continue;
					}
					if (format.charAt(i + 1) != 's')
						throw new CIVLSyntaxException("The format:%"
								+ format.charAt(i + 1)
								+ " is not allowed in printf",
								expressions[0].getSource());
				}
			}
			try {
				output.printf(format, arguments.toArray());
			} catch (Exception e) {
				throw new CIVLInternalException("unexpected error in printf",
						expressions[0].getSource());
			}
		}
		return state;
	}
}
