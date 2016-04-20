package edu.udel.cis.vsl.civl.semantics.IF;

import java.util.Set;

import edu.udel.cis.vsl.civl.err.CIVLExecutionException;
import edu.udel.cis.vsl.civl.err.CIVLExecutionException.ErrorKind;
import edu.udel.cis.vsl.civl.err.CIVLInternalException;
import edu.udel.cis.vsl.civl.err.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.kripke.Enabler;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.statement.WaitStatement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.semantics.Evaluation;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.util.Pair;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public interface Evaluator {

	/**
	 * Given a pointer value, dereferences it in the given state to yield the
	 * symbolic expression value stored at the referenced location.
	 * 
	 * @param state
	 *            a CIVL model state
	 * @param pointer
	 *            a pointer value which refers to some sub-structure in the
	 *            state
	 * @return the value pointed to
	 * @throws UnsatisfiablePathConditionException
	 */
	Evaluation dereference(CIVLSource source, State state,
			SymbolicExpression pointer)
			throws UnsatisfiablePathConditionException;

	/**
	 * Evaluates the expression and returns the result, which is a symbolic
	 * expression value.
	 * 
	 * If a potential error is encountered while evaluating the expression (e.g.
	 * possible division by 0 in x/y), the error is logged, a correcting side
	 * effect (e.g. y!=0) is added to the path condition, and execution
	 * continues. It is possible for the side effect to make the path condition
	 * unsatisfiable. When this happens, an UnsatisfiablePathConditionException
	 * is thrown.
	 * 
	 * @param state
	 *            the state in which the evaluation takes place
	 * @param pid
	 *            the PID of the process which is evaluating the expression
	 * @param expression
	 *            the (static) expression being evaluated
	 * @return the result of the evaluation
	 * @throws UnsatisfiablePathConditionException
	 *             if a side effect that results from evaluating the expression
	 *             causes the path condition to become unsatisfiable
	 */
	Evaluation evaluate(State state, int pid, Expression expression)
			throws UnsatisfiablePathConditionException;

	/**
	 * Evaluate the size of a CIVL type.
	 * 
	 * TODO is this necessarily public?
	 * 
	 * @param source
	 *            The source code element to be used for error report.
	 * @param state
	 *            The state where the evaluation happens.
	 * @param pid
	 *            The ID of the process that triggers the evaluation.
	 * @param type
	 *            The CIVL type whose size is to be evaluated.
	 * @return the result of the evaluation, including the symbolic expression
	 *         of the size of the type and a state
	 * @throws UnsatisfiablePathConditionException
	 */
	Evaluation evaluateSizeofType(CIVLSource source, State state, int pid,
			CIVLType type) throws UnsatisfiablePathConditionException;

	/**
	 * 
	 * Gets a Java concrete int from a symbolic expression or throws exception.
	 * 
	 * @param expression
	 *            a numeric expression expected to hold concrete int value
	 * @return the concrete int
	 * @throws CIVLInternalException
	 *             if a concrete integer value cannot be extracted
	 */
	int extractInt(CIVLSource source, NumericExpression expression);

	/**
	 * Look up a given communicator to find the rank of a certain process. TODO
	 * removed after gcomm/comm is implemented.
	 * 
	 * @param comm
	 * @param pid
	 * @return
	 */
	int findRank(SymbolicExpression comm, int pid);

	/**
	 * Returns the parent pointer of the given pointer, or null if the given
	 * pointer is a variable pointer (i.e., has no parent pointer). TODO move to
	 * Libcivlc?
	 * 
	 * @param pointer
	 *            any pointer value
	 * @return parent pointer or null
	 */
	SymbolicExpression getParentPointer(SymbolicExpression pointer);

	/**
	 * Given a pointer value, returns the dynamic scope ID component of that
	 * pointer value.
	 * 
	 * @param pointer
	 *            a pointer value
	 * @return the dynamic scope ID component of that pointer value
	 */
	int getScopeId(CIVLSource source, SymbolicExpression pointer);

	/**
	 * Given an array, a start index, and end index, returns the array which is
	 * the subsequence of the given array consisting of the elements in
	 * positions start index through end index minus one. The length of the new
	 * array is endIndex - startIndex. TODO move to libcivlc?
	 * 
	 * @param array
	 * @param startIndex
	 * @param endIndex
	 * @param assumption
	 * @param source
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	SymbolicExpression getSubArray(SymbolicExpression array,
			NumericExpression startIndex, NumericExpression endIndex,
			State state, CIVLSource source)
			throws UnsatisfiablePathConditionException;

	/**
	 * Given a pointer value, returns the symbolic reference component of that
	 * value. The "symRef" refers to a sub-structure of the variable pointed to.
	 * 
	 * @param pointer
	 *            a pointer value
	 * @return the symRef component
	 */
	ReferenceExpression getSymRef(SymbolicExpression pointer);

	/**
	 * Given a pointer value, returns the variable ID component of that value.
	 * 
	 * @param pointer
	 *            a pointer value
	 * @return the variable ID component of that value
	 */
	int getVariableId(CIVLSource source, SymbolicExpression pointer);

	/**
	 * Look up a given communicator to find the rank of a certain process. TODO
	 * remove this method when gcomm/comm is implemented.
	 * 
	 * @param comm
	 * @param pid
	 * @return
	 */
	boolean isProcInCommWithRank(SymbolicExpression comm, int pid, int rank);

	/**
	 * Calculate the ID of the process that a given wait statement is waiting
	 * for.
	 * 
	 * @param state
	 *            The current state.
	 * @param p
	 *            The process that the wait statement belongs to.
	 * @param wait
	 *            The wait statement to be checked.
	 * @return The ID of the process that the wait statement is waiting for.
	 */
	int joinedIDofWait(State state, ProcessState p, WaitStatement wait);

	/**
	 * Report a (possible) error detected in the course of evaluating an
	 * expression.
	 * 
	 * Protocol for checking conditions and reporting and recovering from
	 * errors. First, check some condition holds and call the result of that
	 * check "condsat", which may be YES, NO, or MAYBE. If condsat is YES,
	 * proceed. Otherwise, there is a problem: call this method.
	 * 
	 * This method first checks the satisfiability of the path condition, call
	 * the result "pcsat". Logs a violation with certainty determined as
	 * follows:
	 * <ul>
	 * <li>pcsat=YES && condsat=NO : certainty=PROVEABLE</li>
	 * <li>pcsat=YES && condsat=MAYBE : certainty=MAYBE</li>
	 * <li>pcsat=MAYBE && condsat=NO : certainty=MAYBE</li>
	 * <li>pcsat=MAYBE && condsat=MAYBE : certainty=MAYBE</li>
	 * <li>pcsat=NO: no error to report</li>
	 * </ul>
	 * 
	 * Returns the state obtained by adding the claim to the pc of the given
	 * state.
	 * 
	 * TODO: move this to its own package, like log, make public
	 * 
	 */
	State logError(CIVLSource source, State state, BooleanExpression claim,
			ResultType resultType, ErrorKind errorKind, String message)
			throws UnsatisfiablePathConditionException;

	/**
	 * Compute the reachable memory units of an expression recursively.
	 * 
	 * @param state
	 *            The state where the computation happens.
	 * @param pid
	 *            The ID of the process that the expression belongs to.
	 * @param expression
	 *            The expression whose impact memory units are to be computed.
	 * @param memoryUnits
	 *            The set of memory units reachable by the expression.
	 * @throws UnsatisfiablePathConditionException
	 */
	void memoryUnitsOfExpression(State state, int pid, Expression expression,
			Set<SymbolicExpression> memoryUnits)
			throws UnsatisfiablePathConditionException;

	/**
	 * Compute reachable memory units by referencing a variable at a certain
	 * state. For example, given int x = 9; int* y = &x; int *z = y; Then the
	 * reachable memory units from z is {&z, &y, &x}.
	 * 
	 * @param variableValue
	 *            The value of the variable.
	 * @param dyScopeID
	 *            The dynamic scope id of the variable.
	 * @param vid
	 *            The id of the variable in the scope.
	 * @param state
	 *            The state where the computation happens.
	 * @return The set of memory units that reachable from the given variable.
	 */
	Set<SymbolicExpression> memoryUnitsOfVariable(
			SymbolicExpression variableValue, int dyScopeID, int vid,
			State state);

	/**
	 * The model factory should be the unqiue one used in the system.
	 * 
	 * @return The model factory of the evaluator.
	 */
	ModelFactory modelFactory();

	/**
	 * Given a non-trivial pointer, i.e., a pointer to some location inside an
	 * object, returns the parent pointer. For example, a pointer to an array
	 * element returns the pointer to the array.
	 * 
	 * @param pointer
	 *            non-trivial pointer
	 * @return pointer to parent
	 * @throws CIVLInternalException
	 *             if pointer is trivial
	 */
	SymbolicExpression parentPointer(CIVLSource source,
			SymbolicExpression pointer);

	/**
	 * Computes the set of process id's in a given communicator with the same
	 * rank as a certain process.
	 * 
	 * @param comm
	 *            The communicator.
	 * @param pid
	 *            The process to be checked (including in the result set)
	 * @param state
	 *            The state where the computation happens.
	 * @return The set of process IDs that shares the same rank in the
	 *         communciator.
	 */
	Set<Integer> processesOfSameRankInComm(SymbolicExpression comm, int pid,
			int rank);

	/**
	 * Creates a pointer value by evaluating a left-hand-side expression in the
	 * given state.
	 * 
	 * @param state
	 *            a CIVL model state
	 * @param pid
	 *            the process ID of the process in which this evaluation is
	 *            taking place
	 * @param operand
	 *            the left hand side expression we are taking the address of
	 * @return the pointer value
	 * @throws UnsatisfiablePathConditionException
	 */
	Evaluation reference(State state, int pid, LHSExpression operand)
			throws UnsatisfiablePathConditionException;

	/**
	 * Returns the dynamic type pointed to by a pointer. Can be used even if the
	 * pointer can't be dereferenced (because it points off the end of an
	 * object, for example).
	 * 
	 * @param source
	 *            The source code element to be used in the error report.
	 * @param state
	 *            The state where the computation happens.
	 * @param pointer
	 *            The symbolic representation of the pointer whose type is to be
	 *            computed.
	 * @return The symbolic type that the given pointer is pointing to.
	 */
	SymbolicType referencedType(CIVLSource source, State state,
			SymbolicExpression pointer);

	/**
	 * Writes the given execution exception to the log.
	 * 
	 * @param err
	 *            a CIVL execution exception
	 */
	void reportError(CIVLExecutionException err);

	/**
	 * Update the option for whether to solve for concrete counterexamples or
	 * not.
	 * 
	 * @param value
	 *            The option (true of false).
	 */
	void setSolve(boolean value);

	/**
	 * Returns the pointer value obtained by replacing the symRef component of
	 * the given pointer value with the given symRef.
	 * 
	 * @param pointer
	 *            a pointer value
	 * @param symRef
	 *            a symbolic refererence expression
	 * @return the pointer obtained by modifying the given one by replacing its
	 *         symRef field with the given symRef
	 */
	SymbolicExpression setSymRef(SymbolicExpression pointer,
			ReferenceExpression symRef);

	/**
	 * Compute the symbolic representation of the size of a given symbolic type.
	 * 
	 * @param source
	 *            The source code element to be used in the error report (if
	 *            any).
	 * @param type
	 *            The symbolic type whose size is to evaluated.
	 * @return The symbolic representation of the symbolic type.
	 */
	NumericExpression sizeof(CIVLSource source, SymbolicType type);

	/**
	 * The state factory should be the unique one used in the system.
	 * 
	 * @return The state factory of the evaluator.
	 */
	StateFactory stateFactory();

	/**
	 * The symbolic universe should be the unique one used in the system.
	 * 
	 * @return The symbolic universe of the evaluator.
	 */
	SymbolicUniverse universe();

	// void setExecutor(Executor executor);

	void logSimpleError(CIVLSource source, State state, ErrorKind errorKind,
			String message) throws UnsatisfiablePathConditionException;

	SymbolicExpression heapPointer(CIVLSource source, State state,
			SymbolicExpression scopeValue)
			throws UnsatisfiablePathConditionException;

	SymbolicExpression heapValue(CIVLSource source, State state,
			SymbolicExpression scopeValue)
			throws UnsatisfiablePathConditionException;
	
	SymbolicExpression initialHeapValue();

	void setEnabler(Enabler enabler);

	Pair<State, CIVLFunction> evaluateFunctionExpression(State state, int pid,
			Expression functionExpression)
			throws UnsatisfiablePathConditionException;
}
