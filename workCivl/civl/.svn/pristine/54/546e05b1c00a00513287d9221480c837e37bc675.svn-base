/**
 * 
 */
package edu.udel.cis.vsl.civl.semantics;

import java.util.Vector;

import edu.udel.cis.vsl.civl.err.CIVLExecutionException.Certainty;
import edu.udel.cis.vsl.civl.err.CIVLExecutionException.ErrorKind;
import edu.udel.cis.vsl.civl.err.CIVLInternalException;
import edu.udel.cis.vsl.civl.err.CIVLStateException;
import edu.udel.cis.vsl.civl.err.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.library.civlc.Libcivlc;
import edu.udel.cis.vsl.civl.log.ErrorLog;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.SystemFunction;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.AssertStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.AssignStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.AssumeStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ChooseStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.MallocStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.NoopStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ReturnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.statement.WaitStatement;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.state.Process;
import edu.udel.cis.vsl.civl.state.StackEntry;
import edu.udel.cis.vsl.civl.state.State;
import edu.udel.cis.vsl.civl.state.StateFactoryIF;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SARLException;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.ValidityResult;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * An executor is used to execute a CIVL statement. The basic method provided
 * takes a state and a statement, and modifies the state according to the
 * semantics of that statement.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class Executor {

	// Fields..............................................................

	private ModelFactory modelFactory;

	/** The symbolic universe used to maange all symbolic expressions. */
	private SymbolicUniverse symbolicUniverse;

	/** The factory used to produce and manipulate model states. */
	private StateFactoryIF stateFactory;

	/** The Evaluator used to evaluate expressions. */
	private Evaluator evaluator;

	/**
	 * Log used to record property violations encountered as the model is
	 * executed.
	 */
	private ErrorLog log;

	/**
	 * The loader used to find Executors for system functions declared in
	 * libraries.
	 */
	private LibraryExecutorLoader loader;

	private Libcivlc civlcExecutor;

	// Constructors........................................................

	/**
	 * Create a new executor.
	 * 
	 * @param model
	 *            The model being executed.
	 * @param symbolicUniverse
	 *            A symbolic universe for creating new values.
	 * @param stateFactory
	 *            A state factory. Used by the Executor to create new processes.
	 * @param prover
	 *            A theorem prover for checking assertions.
	 */
	public Executor(ModelFactory modelFactory, StateFactoryIF stateFactory,
			ErrorLog log, LibraryExecutorLoader loader) {
		this.symbolicUniverse = modelFactory.universe();
		this.stateFactory = stateFactory;
		this.modelFactory = modelFactory;
		this.evaluator = new Evaluator(modelFactory, stateFactory, log);
		this.log = log;
		this.loader = loader;
		this.civlcExecutor = (Libcivlc) loader
				.getLibraryExecutor("civlc", this);
	}

	/**
	 * Create a new executor with null library loader.
	 * 
	 * @param model
	 *            The model being executed.
	 * @param symbolicUniverse
	 *            A symbolic universe for creating new values.
	 * @param stateFactory
	 *            A state factory. Used by the Executor to create new processes.
	 * @param prover
	 *            A theorem prover for checking assertions.
	 */
	public Executor(ModelFactory modelFactory, StateFactoryIF stateFactory,
			ErrorLog log) {
		this(modelFactory, stateFactory, log, null);
	}

	// Helper methods...

	/**
	 * Transition a process from one location to another. If the new location is
	 * in a different scope, create a new scope or move to the parent scope as
	 * necessary.
	 * 
	 * @param state
	 *            The old state.
	 * @param process
	 *            The process undergoing the transition.
	 * @param target
	 *            The end location of the transition.
	 * @return A new state where the process is at the target location.
	 */
	private State transition(State state, Process process, Location target) {
		state = stateFactory.setLocation(state, process.id(), target);
		// state = stateFactory.canonic(state);
		return state;
	}

	/**
	 * Assigns a value to the referenced cell in the state. Returns a new state
	 * which is equivalent to the old state except that the memory specified by
	 * the given pointer value is assigned the given value.
	 * 
	 * @param state
	 *            a CIVL model state
	 * @param pointer
	 *            a pointer value
	 * @param value
	 *            a value to be assigned to the referenced memory location
	 * @return the new state
	 */
	public State assign(CIVLSource source, State state,
			SymbolicExpression pointer, SymbolicExpression value) {
		int vid = evaluator.getVariableId(source, pointer);
		int sid = evaluator.getScopeId(source, pointer);
		ReferenceExpression symRef = evaluator.getSymRef(pointer);
		State result;

		if (symRef.isIdentityReference()) {
			result = stateFactory.setVariable(state, vid, sid, value);
		} else {
			SymbolicExpression oldVariableValue = state.getVariableValue(sid,
					vid);
			SymbolicExpression newVariableValue = symbolicUniverse.assign(
					oldVariableValue, symRef, value);

			result = stateFactory
					.setVariable(state, vid, sid, newVariableValue);
		}
		return result;
	}

	/**
	 * Assigns a value to the memory location specified by the given
	 * left-hand-side expression.
	 * 
	 * @param state
	 *            a CIVL model state
	 * @param pid
	 *            the PID of the process executing the assignment
	 * @param lhs
	 *            a left-hand-side expression
	 * @param value
	 *            the value being assigned to the left-hand-side
	 * @return the new state
	 * @throws UnsatisfiablePathConditionException
	 */
	public State assign(State state, int pid, LHSExpression lhs,
			SymbolicExpression value)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluator.reference(state, pid, lhs);

		return assign(lhs.getSource(), eval.state, eval.value, value);
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
		Process process = state.process(pid);
		Evaluation eval = evaluator.evaluate(state, pid, statement.rhs());

		state = assign(eval.state, pid, statement.getLhs(), eval.value);
		state = transition(state, process, statement.target());
		// state = stateFactory.canonic(state);
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
					((SystemFunction) statement.function()).getLibrary(), this);

			state = executor.execute(state, pid, statement);
			state = transition(state, state.process(pid), statement.target());
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
			state = stateFactory.pushCallStack(state, pid, function, arguments);
		}
		return state;
	}

	private State executeMalloc(State state, int pid, MallocStatement statement)
			throws UnsatisfiablePathConditionException {
		State result = civlcExecutor.executeMalloc(state, pid, statement);

		result = transition(result, result.process(pid), statement.target());
		return result;
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
		Process process = state.process(pid);
		CIVLFunction function = statement.function();
		int newPid = state.numProcs();
		Vector<Expression> argumentExpressions = statement.arguments();
		int numArgs = argumentExpressions.size();
		SymbolicExpression[] arguments = new SymbolicExpression[numArgs];

		assert !statement.isCall();
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
		state = transition(state, process, statement.target());
		// state = stateFactory.canonic(state);
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

		state = transition(eval.state, state.process(pid), statement.target());
		state = stateFactory.removeProcess(state, joinedPid);
		// state = stateFactory.canonic(state);
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
		Process process;
		SymbolicExpression returnValue;

		if (expr == null) {
			returnValue = null;
		} else {
			Evaluation eval = evaluator.evaluate(state, pid, expr);

			returnValue = eval.value;
			state = eval.state;
		}
		state = stateFactory.popCallStack(state, pid);
		process = state.process(pid);
		if (!process.hasEmptyStack()) {
			StackEntry returnContext = process.peekStack();
			Location returnLocation = returnContext.location();
			CallOrSpawnStatement call = (CallOrSpawnStatement) returnLocation
					.getSoleOutgoing();

			if (call.lhs() != null)
				state = assign(state, pid, call.lhs(), returnValue);
			state = stateFactory.setLocation(state, pid, call.target());
		}
		// state = stateFactory.canonic(state);
		return state;
	}

	private State executeAssume(State state, int pid, AssumeStatement statement)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluator.evaluate(state, pid,
				statement.getExpression());
		BooleanExpression assumeValue = (BooleanExpression) eval.value;
		BooleanExpression oldPathCondition, newPathCondition;

		state = eval.state;
		oldPathCondition = state.pathCondition();
		newPathCondition = symbolicUniverse.and(oldPathCondition, assumeValue);
		state = stateFactory.setPathCondition(state, newPathCondition);
		state = transition(state, state.process(pid), statement.target());
		return state;
	}

	private State executeAssert(State state, int pid, AssertStatement statement)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluator.evaluate(state, pid,
				statement.getExpression());
		BooleanExpression assertValue = (BooleanExpression) eval.value;
		Reasoner reasoner;
		ValidityResult valid;
		ResultType resultType;

		state = eval.state;
		reasoner = symbolicUniverse.reasoner(state.pathCondition());
		valid = reasoner.valid(assertValue);
		resultType = valid.getResultType();
		if (resultType != ResultType.YES) {
			Certainty certainty = resultType == ResultType.NO ? Certainty.PROVEABLE
					: Certainty.MAYBE;

			log.report(new CIVLStateException(ErrorKind.ASSERTION_VIOLATION,
					certainty, "Cannot prove assertion holds: "
							+ statement.toString() + "\n  Path condition: "
							+ state.pathCondition() + "\n  Assertion: "
							+ assertValue + "\n", state, statement.getSource()));
			state = stateFactory.setPathCondition(state,
					symbolicUniverse.and(state.pathCondition(), assertValue));
		}
		state = transition(state, state.process(pid), statement.target());
		return state;
	}

	// Exported Methods................................................

	/**
	 * Execute a choose statement. This is like an assignment statement where
	 * the variable gets assigned a particular value between 0 and arg-1,
	 * inclusive. The value is assigned for each transition from the choose
	 * source location by the Enabler.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The process id of the currently executing process.
	 * @param statement
	 *            A choose statement to be executed.
	 * @param value
	 *            The value assigned to the variable for this particular
	 *            transition. This concrete value should be provided by the
	 *            enabler.
	 * @return The updated state of the program.
	 * @throws UnsatisfiablePathConditionException
	 */
	public State executeChoose(State state, int pid, ChooseStatement statement,
			SymbolicExpression value)
			throws UnsatisfiablePathConditionException {
		Process process = state.process(pid);

		state = assign(state, pid, statement.getLhs(), value);
		state = transition(state, process, statement.target());
		return state;
	}

	/**
	 * @return The state factory associated with this executor.
	 */
	public StateFactoryIF stateFactory() {
		return stateFactory;
	}

	/**
	 * @return The symbolic universe associated with this executor.
	 */
	public SymbolicUniverse universe() {
		return symbolicUniverse;
	}

	/**
	 * @return The evaluator used by this executor.
	 * @return
	 */
	public Evaluator evaluator() {
		return evaluator;
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
		if (statement instanceof AssumeStatement) {
			return executeAssume(state, pid, (AssumeStatement) statement);
		} else if (statement instanceof AssertStatement) {
			return executeAssert(state, pid, (AssertStatement) statement);
		} else if (statement instanceof CallOrSpawnStatement) {
			CallOrSpawnStatement call = (CallOrSpawnStatement) statement;

			if (call.isCall())
				return executeCall(state, pid, call);
			else
				return executeSpawn(state, pid, call);
		} else if (statement instanceof AssignStatement) {
			return executeAssign(state, pid, (AssignStatement) statement);
		} else if (statement instanceof WaitStatement) {
			return executeWait(state, pid, (WaitStatement) statement);
		} else if (statement instanceof ReturnStatement) {
			return executeReturn(state, pid, (ReturnStatement) statement);
		} else if (statement instanceof NoopStatement) {
			state = transition(state, state.process(pid), statement.target());

			return state;
		} else if (statement instanceof MallocStatement) {
			return executeMalloc(state, pid, (MallocStatement) statement);
		} else if (statement instanceof ChooseStatement) {
			throw new CIVLInternalException("Should be unreachable", statement);
		} else
			throw new CIVLInternalException("Unknown statement kind", statement);
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
	public State execute(State state, int pid, Statement statement)
			throws UnsatisfiablePathConditionException {
		try {
			return executeWork(state, pid, statement);
		} catch (SARLException e) {
			e.printStackTrace(System.err);
			System.err.flush();
			throw new CIVLInternalException("SARL exception: " + e, statement);
		}
	}

	public LibraryExecutor libraryExecutor(CallOrSpawnStatement statement) {
		String library;

		assert statement.function() instanceof SystemFunction;
		library = ((SystemFunction) statement.function()).getLibrary();
		if (library.equals("civlc")) {
			return civlcExecutor;
		} else {
			throw new CIVLInternalException("Unknown library: " + library,
					statement);
		}
	}

}
