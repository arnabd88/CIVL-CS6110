package edu.udel.cis.vsl.civl.semantics.IF;

import java.io.PrintStream;
import java.util.List;

import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

public interface Executor {

	/**
	 * Assigns a value to the referenced cell in the state. Returns a new state
	 * which is equivalent to the old state except that the memory specified by
	 * the given pointer value is assigned the given value.
	 * 
	 * @param source
	 *            the source code information for error report
	 * @param state
	 *            a CIVL model state
	 * @param process
	 *            the process information (process name + PID) for error report
	 * @param pointer
	 *            a pointer value
	 * @param value
	 *            a value to be assigned to the referenced memory location
	 * @return the new state
	 * @throws UnsatisfiablePathConditionException
	 */
	State assign(CIVLSource source, State state, String process,
			SymbolicExpression pointer, SymbolicExpression value)
			throws UnsatisfiablePathConditionException;

	/**
	 * Assigns a value to the memory location specified by the given
	 * left-hand-side expression.
	 * 
	 * @param state
	 *            a CIVL model state
	 * @param pid
	 *            the PID of the process executing the assignment
	 * @param process
	 *            the process information (process name + PID) for error report
	 * @param lhs
	 *            a left-hand-side expression
	 * @param value
	 *            the value being assigned to the left-hand-side
	 * @return the new state
	 * @throws UnsatisfiablePathConditionException
	 */
	State assign(State state, int pid, String process, LHSExpression lhs,
			SymbolicExpression value)
			throws UnsatisfiablePathConditionException;

	/**
	 * @return The state factory associated with this executor.
	 */
	StateFactory stateFactory();

	/**
	 * @return The evaluator used by this executor.
	 */
	Evaluator evaluator();

	/**
	 * Returns the number of "steps" executed since this Executor was created.
	 * 
	 * @return the number of steps executed
	 */
	long getNumSteps();

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
	State malloc(CIVLSource source, State state, int pid, String process,
			LHSExpression lhs, Expression scopeExpression,
			SymbolicExpression scopeValue, CIVLType objectType,
			SymbolicExpression objectValue)
			throws UnsatisfiablePathConditionException;

	/**
	 * Adds a new object to the heap of a certain scope; returns the pointer of
	 * the object in the heap.
	 * 
	 * @param source
	 *            The source code element to be used to report errors.
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the process where this computation happens.
	 * @param scopeExpression
	 *            The static expression of the scope value.
	 * @param scopeValue
	 *            The symbolic expression of the scope.
	 * @param objectType
	 *            The CIVL type of the object to be added, needed to decide the
	 *            field index in the heap.
	 * @param objectValue
	 *            The object to be added to the heap.
	 * @return The new state after allocating the specified object in the heap
	 *         and the pointer of the object in the heap.
	 * @throws UnsatisfiablePathConditionException
	 */
	Pair<State, SymbolicExpression> malloc(CIVLSource source, State state,
			int pid, String process, Expression scopeExpression,
			SymbolicExpression scopeValue, CIVLType objectType,
			SymbolicExpression objectValue)
			throws UnsatisfiablePathConditionException;

	/**
	 * Returns the state that results from executing the statement, or null if
	 * path condition becomes unsatisfiable.
	 * 
	 * @param state
	 *            the state that the transition emanates from
	 * @param pid
	 *            the PID of the process that the transition
	 * @param transition
	 *            a deterministic transition to be executed
	 * @return The state after the transition is executed.
	 */
	State execute(State state, int pid, Transition transition)
			throws UnsatisfiablePathConditionException;

	/**
	 * Returns the error logger used by this executor.
	 * 
	 * @return The error logger used by this executor.
	 */
	CIVLErrorLogger errorLogger();

	State execute_printf(CIVLSource source, State state, int pid,
			String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException;

	List<Format> splitFormat(CIVLSource source, StringBuffer formatBuffer);

	/**
	 * If there are insufficient arguments for the format, the behavior is
	 * undefined. If the format is exhausted while arguments remain, the excess
	 * arguments are evaluated (as always) but are otherwise ignored.
	 * 
	 * @param printStream
	 * @param source
	 * @param formats
	 * @param arguments
	 */
	void printf(PrintStream printStream, CIVLSource source, String process,
			List<Format> formats, List<StringBuffer> arguments);

	/**
	 * A lowest level contract violation error reporting function: provides
	 * basic contract violation error reporting format.
	 * 
	 * @param state
	 *            The state where the evaluation is on
	 * @param source
	 *            The CIVLSource of the contract
	 * @param place
	 *            The place of the process in the group (Or PID for regular
	 *            non-collective contract)
	 * @param process
	 *            The String identifier of the process
	 * @param resultType
	 *            The result type of the reasoning result
	 * @param assertValue
	 *            The value of the evaluated condition
	 * @param violatedCondition
	 *            The expression of the condition
	 * @param errorKind
	 *            The corresponding error kind: CONTRACT for regular contract
	 *            violation or MPI_ERROR for collective contract violation
	 * @param groupString
	 *            The String of the group of processes, only significant when
	 *            errorKind == MPI_ERROR
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	State reportContractViolation(State state, CIVLSource source, int place,
			ResultType resultType, BooleanExpression assertValue,
			Expression violatedCondition, ErrorKind errorKind,
			String groupString) throws UnsatisfiablePathConditionException;
}
