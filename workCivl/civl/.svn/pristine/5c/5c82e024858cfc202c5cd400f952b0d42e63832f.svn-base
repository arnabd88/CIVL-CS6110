package edu.udel.cis.vsl.civl.semantics.IF;

import edu.udel.cis.vsl.civl.err.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.kripke.Enabler;
import edu.udel.cis.vsl.civl.library.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.ChooseStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.common.statement.StatementList;
import edu.udel.cis.vsl.civl.semantics.CommonExecutor.StateStatusKind;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.util.Pair;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

public interface Executor {
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
	 * @throws UnsatisfiablePathConditionException
	 */
	State assign(CIVLSource source, State state, SymbolicExpression pointer,
			SymbolicExpression value)
			throws UnsatisfiablePathConditionException;

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
	State assign(State state, int pid, LHSExpression lhs,
			SymbolicExpression value)
			throws UnsatisfiablePathConditionException;

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
	State executeChoose(State state, int pid, ChooseStatement statement,
			SymbolicExpression value)
			throws UnsatisfiablePathConditionException;

	/**
	 * @return The state factory associated with this executor.
	 */
	StateFactory stateFactory();

	/**
	 * @return The symbolic universe associated with this executor.
	 */
	SymbolicUniverse universe();

	/**
	 * @return The evaluator used by this executor.
	 */
	Evaluator evaluator();

	/**
	 * @return The model factory used by this executor.
	 */
	ModelFactory modelFactory();

	State executeStatementList(State state, int pid, StatementList statement,
			SymbolicExpression value)
			throws UnsatisfiablePathConditionException;

	/**
	 * Returns the state that results from executing the statement, or null if
	 * path condition becomes unsatisfiable.
	 * 
	 * @param state
	 * @param pid
	 * @param statement
	 * @return
	 */
	State execute(State state, int pid, Statement statement)
			throws UnsatisfiablePathConditionException;

	// LibraryExecutor libraryExecutor(CallOrSpawnStatement statement);
	//
	// LibraryExecutor libraryExecutor(CIVLSource source, String library);

	// Evaluation evaluateSystemGuard(State state, int pid,
	// SystemGuardExpression systemGuard);

	/**
	 * Execute a statement from a certain state and return the resulting state
	 * TODO make sure the pid is never changed or return the new pid if changed
	 * 
	 * @param state
	 *            The state to execute the statement with
	 * @param location
	 *            The location of the statement, satisfying that
	 *            <code>s.source() == location</code>.
	 * @param s
	 *            The statement to be executed
	 * @param pid
	 *            The id of the process that the statement <code>s</code>
	 *            belongs to. Precondition:
	 *            <code>state.getProcessState(pid).getLocation() == location</code>
	 * @return
	 */
	Pair<StateStatusKind, State> executeStatement(State state,
			Location location, Statement s, int pid);

	/**
	 * Returns the number of "steps" executed since this Executor was created.
	 * 
	 * @return the number of steps executed
	 */
	long getNumSteps();

	/**
	 * Update the enabler to be used in the executor.
	 * 
	 * @param enabler
	 *            the enabler to be used.
	 */
	void setEnabler(Enabler enabler);

	/**
	 * The enabler used in the executor should be the unique one used in the
	 * whole system.
	 * 
	 * @return The enabler used in the executor.
	 */
	Enabler enabler();

	/**
	 * Adds a new object to the heap of a certain scope; sets the pointer of the
	 * object in the heap to the provided left-hand-side expression (or does
	 * nothing if no left-hand-side expression is specified).
	 * 
	 * @param source
	 *            The source code element to be used to report errors.
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the process where this computation happens.
	 * @param lhs
	 *            The left-hand-side expression to store the pointer to the
	 *            added object.
	 * @param scopeExpression
	 *            The static expression of the scope value.
	 * @param scopeValue
	 *            The symbolic expression of the scope.
	 * @param objectType
	 *            The CIVL type of the object to be added, needed to decide the
	 *            field index in the heap.
	 * @param objectValue
	 *            The object to be added to the heap.
	 * @return The new state after adding the given object to the heap in the
	 *         given scope.
	 * @throws UnsatisfiablePathConditionException
	 */
	State malloc(CIVLSource source, State state, int pid, LHSExpression lhs,
			Expression scopeExpression, SymbolicExpression scopeValue,
			CIVLType objectType, SymbolicExpression objectValue)
			throws UnsatisfiablePathConditionException;

	LibraryExecutor libraryExecutor(CIVLSource source, String library);
}
