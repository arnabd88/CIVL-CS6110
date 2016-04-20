/**
 * 
 */
package edu.udel.cis.vsl.civl.semantics;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Vector;

import edu.udel.cis.vsl.civl.log.ErrorLog;
import edu.udel.cis.vsl.civl.log.ExecutionException;
import edu.udel.cis.vsl.civl.model.IF.Function;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.SystemFunction;
import edu.udel.cis.vsl.civl.model.IF.expression.ArrayIndexExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.StringLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.AssertStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.AssignStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.AssumeStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.CallStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ChooseStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ForkStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.JoinStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ReturnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.type.PointerType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.state.DynamicScope;
import edu.udel.cis.vsl.civl.state.Process;
import edu.udel.cis.vsl.civl.state.StackEntry;
import edu.udel.cis.vsl.civl.state.State;
import edu.udel.cis.vsl.civl.state.StateFactoryIF;
import edu.udel.cis.vsl.civl.util.ExecutionProblem.Certainty;
import edu.udel.cis.vsl.civl.util.ExecutionProblem.ErrorKind;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.ValidityResult;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * An executor is used to execute a Chapel statement. The basic method provided
 * takes a state and a statement, and modifies the state according to the
 * semantics of that statement.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class Executor {

	private Model model;
	private SymbolicUniverse symbolicUniverse;
	private StateFactoryIF stateFactory;
	private Evaluator evaluator;
	private Vector<State> finalStates = new Vector<State>();
	private ErrorLog log;
	private SymbolicTupleType processType;
	private String pidPrefix = "PID_";
	private LibraryExecutorLoader loader;

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
	public Executor(Model model, SymbolicUniverse symbolicUniverse,
			StateFactoryIF stateFactory, ErrorLog log,
			LibraryExecutorLoader loader) {
		List<SymbolicType> processTypeList = new Vector<SymbolicType>();

		this.model = model;
		this.symbolicUniverse = symbolicUniverse;
		this.stateFactory = stateFactory;
		this.evaluator = new Evaluator(symbolicUniverse, log);
		this.log = log;
		this.loader = loader;
		processTypeList.add(symbolicUniverse.integerType());
		processType = symbolicUniverse.tupleType(
				symbolicUniverse.stringObject("process"), processTypeList);
	}

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
	public Executor(Model model, SymbolicUniverse symbolicUniverse,
			StateFactoryIF stateFactory, ErrorLog log) {
		List<SymbolicType> processTypeList = new Vector<SymbolicType>();

		this.model = model;
		this.symbolicUniverse = symbolicUniverse;
		this.stateFactory = stateFactory;
		this.evaluator = new Evaluator(symbolicUniverse, log);
		this.log = log;
		processTypeList.add(symbolicUniverse.integerType());
		processType = symbolicUniverse.tupleType(
				symbolicUniverse.stringObject("process"), processTypeList);
	}

	/**
	 * Create a new executor.
	 * 
	 * @param symbolicUniverse
	 *            A symbolic universe for creating new values.
	 * @param stateFactory
	 *            A state factory. Used by the Executor to create new processes.
	 * @param out
	 *            A PrintStream to use for write statements.
	 */
	public Executor(Model model, SymbolicUniverse symbolicUniverse,
			StateFactoryIF stateFactory, PrintStream out) {
		List<SymbolicType> processTypeList = new Vector<SymbolicType>();

		this.model = model;
		this.symbolicUniverse = symbolicUniverse;
		this.stateFactory = stateFactory;
		this.evaluator = new Evaluator(symbolicUniverse, log);
		processTypeList.add(symbolicUniverse.integerType());
		processType = symbolicUniverse.tupleType(
				symbolicUniverse.stringObject("process"), processTypeList);
	}

	/**
	 * Execute an assignment statement. The state will be updated such that the
	 * value of the DynamicVariable has the expression corresponding to the
	 * right hand side of the assignment, and the location of the state will be
	 * updated to the target location of the assignment.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The process id of the currently executing process.
	 * @param statement
	 *            An assignment statement to be executed.
	 * @return The updated state of the program.
	 */
	public State execute(State state, int pid, AssignStatement statement) {
		Process process = state.process(pid);

		state = writeValue(state, pid, statement.getLhs(), statement.rhs());
		state = transition(state, process, statement.target());
		// state = stateFactory.canonic(state);
		return state;
	}

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
	 */
	public State execute(State state, int pid, ChooseStatement statement,
			SymbolicExpression value) {
		Process process = state.process(pid);
		state = writeValue(state, pid, statement.getLhs(), value);
		state = transition(state, process, statement.target());
		return state;
	}

	/**
	 * Execute a call statement. The state will be updated such that the process
	 * is at the start location of the function, a new dynamic scope for the
	 * function is created, and function parameters in the new scope have the
	 * values that are passed as arguments.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The process id of the currently executing process.
	 * @param statement
	 *            A call statement to be executed.
	 * @return The updated state of the program.
	 */
	public State execute(State state, int pid, CallStatement statement) {
		if (statement.function() instanceof SystemFunction) {
			LibraryExecutor executor = loader.getLibraryExecutor(
					((SystemFunction) statement.function()).getLibrary(), this);

			state = executor.execute(state, pid, statement);
		} else {
			Function function = statement.function();
			SymbolicExpression[] arguments;

			arguments = new SymbolicExpression[statement.arguments().size()];
			for (int i = 0; i < statement.arguments().size(); i++) {
				SymbolicExpression expression;

				if (function.parameters().get(i).type() instanceof PointerType) {
					expression = evaluator.reference(state, pid, statement
							.arguments().get(i));
				} else {
					expression = evaluator.evaluate(state, pid, statement
							.arguments().get(i));
				}

				arguments[i] = expression;
			}
			state = stateFactory.pushCallStack(state, pid, function, arguments);
		}
		return state;
	}

	/**
	 * Execute a fork statement. The state will be updated with a new process
	 * whose start location is the beginning of the forked function.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The process id of the currently executing process.
	 * @param statement
	 *            A fork statement to be executed.
	 * @return The updated state of the program.
	 */
	public State execute(State state, int pid, ForkStatement statement) {
		Process process = state.process(pid);
		Function function = null;
		SymbolicExpression[] arguments;
		int newPid;

		for (Function f : model.functions()) {
			// Note: The function is a string literal expression
			if (f.name()
					.name()
					.equals(((StringLiteralExpression) statement.function())
							.value())) {
				function = f;
				break;
			}
		}
		// TODO: Throw exception if function not found.
		arguments = new SymbolicExpression[statement.arguments().size()];
		for (int i = 0; i < statement.arguments().size(); i++) {
			arguments[i] = evaluator.evaluate(state, pid, statement.arguments()
					.get(i));
		}
		state = stateFactory.addProcess(state, function, arguments, pid);
		// Find the new process's id.
		newPid = pid;
		for (Process p : state.processes()) {
			if (p.id() > newPid) {
				newPid = p.id();
			}
		}
		if (statement.lhs() != null) {
			state = writeValue(state, pid, statement.lhs(),
					symbolicUniverse.symbolicConstant(
							symbolicUniverse.stringObject(pidPrefix + newPid),
							processType));
		}
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
	 */
	public State execute(State state, int pid, JoinStatement statement) {
		SymbolicExpression pidExpression = evaluator.evaluate(state, pid,
				statement.process());
		int joinedPid;

		assert pidExpression instanceof SymbolicConstant;
		assert ((SymbolicConstant) pidExpression).name().getString()
				.startsWith(pidPrefix);
		joinedPid = Integer.parseInt(((SymbolicConstant) pidExpression).name()
				.getString().substring(pidPrefix.length()));
		// TODO: Throw exception if not the right type.
		state = stateFactory.removeProcess(state, joinedPid);
		state = transition(state, state.process(pid), statement.target());
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
	 */
	public State execute(State state, int pid, ReturnStatement statement) {
		Process process;
		StackEntry returnContext;
		Location returnLocation;
		CallStatement call = null;
		SymbolicExpression returnExpression = null;

		if (state.process(pid).peekStack().location().function().name().name()
				.equals("_CVT_system")) {
			if (!finalStates.contains(state)) {
				finalStates.add(state);
			}
		}
		if (statement.expression() != null) {
			returnExpression = evaluator.evaluate(state, pid,
					statement.expression());
		}
		state = stateFactory.popCallStack(state, pid);
		process = state.process(pid);
		if (!process.hasEmptyStack()) {
			Iterator<Statement> outgoingIterator;
			returnContext = process.peekStack();
			returnLocation = returnContext.location();
			// Note: the location of the function call should have exactly one
			// outgoing statement, which is a call statement.
			// TODO: Verify this, throw an exception if it's not the case.
			outgoingIterator = returnLocation.outgoing().iterator();
			while (outgoingIterator.hasNext()) {
				Statement outgoingStatement = outgoingIterator.next();

				if (outgoingStatement instanceof CallStatement) {
					if (call == null) {
						call = (CallStatement) outgoingStatement;
					} else {
						throw new RuntimeException(
								"Expected 1 outgoing call statement from "
										+ returnLocation);
					}
				}
			}
			if (call == null) {
				throw new RuntimeException("Cannot return to " + returnLocation
						+ ".  No call statment found.");
			}
			if (call.lhs() != null) {
				state = writeValue(state, pid, call.lhs(), returnExpression);
			}
			state = stateFactory.setLocation(state, pid, call.target());
		}
		// state = stateFactory.canonic(state);
		return state;
	}

	public State execute(State state, int pid, AssumeStatement statement) {
		SymbolicExpression assumeExpression = evaluator.evaluate(state, pid,
				statement.getExpression());

		state = stateFactory.setPathCondition(state, symbolicUniverse.and(
				(BooleanExpression) state.pathCondition(),
				(BooleanExpression) assumeExpression));
		state = transition(state, state.process(pid), statement.target());
		return state;
	}

	public State execute(State state, int pid, AssertStatement statement) {
		SymbolicExpression assertExpression = evaluator.evaluate(state, pid,
				statement.getExpression());
		Reasoner reasoner = symbolicUniverse.reasoner((BooleanExpression) state
				.pathCondition());
		ValidityResult valid = reasoner
				.valid((BooleanExpression) assertExpression);
		// TODO Handle error reporting in a nice way.
		if (valid.getResultType() != ResultType.YES) {
			Certainty certainty;
			ByteArrayOutputStream baos = new ByteArrayOutputStream();
			PrintStream ps = new PrintStream(baos);

			if (valid.getResultType() == ResultType.NO) {
				certainty = Certainty.PROVEABLE;
			} else {
				certainty = Certainty.MAYBE;
			}
			state.print(ps);
			log.report(new ExecutionException(ErrorKind.ASSERTION_VIOLATION,
					certainty, "Cannot prove assertion holds: "
							+ statement.toString() + "\n  Path condition: "
							+ state.pathCondition() + "\n  Assertion: "
							+ assertExpression + "\n\n" + baos.toString()));

		}
		state = transition(state, state.process(pid), statement.target());
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
	public State execute(State state, int pid, Statement statement) {
		Process process;

		if (statement instanceof AssumeStatement) {
			return execute(state, pid, (AssumeStatement) statement);
		} else if (statement instanceof AssertStatement) {
			return execute(state, pid, (AssertStatement) statement);
		} else if (statement instanceof CallStatement) {
			return execute(state, pid, (CallStatement) statement);
		} else if (statement instanceof AssignStatement) {
			return execute(state, pid, (AssignStatement) statement);
		} else if (statement instanceof ForkStatement) {
			return execute(state, pid, (ForkStatement) statement);
		} else if (statement instanceof JoinStatement) {
			return execute(state, pid, (JoinStatement) statement);
		} else if (statement instanceof ReturnStatement) {
			return execute(state, pid, (ReturnStatement) statement);
		}
		// Otherwise, this is a noop.
		process = state.process(pid);
		state = transition(state, process, statement.target());
		// state = stateFactory.canonic(state);
		return state;
	}

	/**
	 * Write a value to a variable.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The process id of the currently executing process.
	 * @param target
	 *            The location where the value should be stored. This should be
	 *            an ArrayIndexExpression or a VariableExpression.
	 * @param value
	 *            An expression for the new value to write.
	 * @return A new state with the value of the target variable modified.
	 */
	private State writeValue(State state, int pid, Expression target,
			Expression value) {
		State result = writeValue(state, pid, target,
				evaluator.evaluate(state, pid, value));

		// result = stateFactory.canonic(result);
		return result;
	}

	/**
	 * Write a value to a variable.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The process id of the currently executing process.
	 * @param target
	 *            The location where the value should be stored. This should be
	 *            an ArrayIndexExpression or a VariableExpression.
	 * @param symbolicValue
	 *            The new symbolic value to write.
	 * @return A new state with the value of the target variable modified.
	 */
	private State writeValue(State state, int pid, Expression target,
			SymbolicExpression symbolicValue) {
		DynamicScope scope = state.getScope(state.process(pid).scope());

		if (target instanceof VariableExpression) {
			Variable variable = ((VariableExpression) target).variable();

			state = stateFactory.setVariable(state, variable, pid,
					symbolicValue);
		} else if (target instanceof ArrayIndexExpression) {
			SymbolicExpression newValue = arrayWriteValue(state, pid,
					(ArrayIndexExpression) target, symbolicValue);

			state = stateFactory.setVariable(state,
					baseArray(scope, (ArrayIndexExpression) target), pid,
					newValue);
		} else if (target instanceof UnaryExpression) {
			Variable variable = evaluator.getVariable(state, pid, target);
			int scopeID = evaluator.getPointerTargetScope(state, pid, target);

			state = stateFactory.setVariable(state, variable, scopeID, pid,
					symbolicValue);
		}
		// TODO: Throw some sort of exception otherwise.
		// state = stateFactory.canonic(state);
		return state;
	}

	/**
	 * Determine the symbolic value that results from writing to an array
	 * position.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The process ID of the currently executing process.
	 * @param arrayIndex
	 *            The expression for the index in the array being modified.
	 * @param value
	 *            The value being written to the array at the specified index.
	 * @return A new symbolic value for the array.
	 */
	private SymbolicExpression arrayWriteValue(State state, int pid,
			ArrayIndexExpression arrayIndex, SymbolicExpression value) {
		SymbolicExpression result = null;
		SymbolicExpression array = evaluator.evaluate(state, pid,
				arrayIndex.array());
		SymbolicExpression index = evaluator.evaluate(state, pid,
				arrayIndex.index());

		while (array.type().equals(evaluator.pointerType())) {
			array = evaluator.dereference(state, pid, array);
		}
		if (arrayIndex.array() instanceof ArrayIndexExpression) {
			result = arrayWriteValue(state, pid,
					(ArrayIndexExpression) arrayIndex.array(),
					symbolicUniverse.arrayWrite(array,
							(NumericExpression) index, value));
		} else {
			result = symbolicUniverse.arrayWrite(array,
					(NumericExpression) index, value);
		}
		return result;
	}

	/**
	 * Get the variable at the base of a (possibly multi-dimensional) array.
	 * 
	 * @param scope
	 *            The dynamic scope containing this array reference.
	 * @param expression
	 *            The array index expression.
	 * @return The variable corresponding to the base of this array.
	 */
	private Variable baseArray(DynamicScope scope,
			ArrayIndexExpression expression) {
		if (expression.array() instanceof ArrayIndexExpression) {
			return baseArray(scope, ((ArrayIndexExpression) expression.array()));
		} else if (expression.array() instanceof VariableExpression) {
			return ((VariableExpression) expression.array()).variable();
		}
		return null;
	}

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
	 * 
	 * @return The final states of the program.
	 */
	public Collection<State> finalStates() {
		return finalStates;
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
}
