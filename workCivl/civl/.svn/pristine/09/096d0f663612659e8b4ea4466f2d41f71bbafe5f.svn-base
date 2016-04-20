package edu.udel.cis.vsl.civl.library.common;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.ValidityResult;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.ArrayElementReference;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NTReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.TupleComponentReference;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;

/**
 * This class provides the common data and operations of library executors.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public abstract class BaseLibraryExecutor extends LibraryComponent implements
		LibraryExecutor {

	/* ************************** Instance Fields ************************** */

	/**
	 * The evaluator for evaluating expressions.
	 */
	protected Evaluator evaluator;

	/**
	 * The primary executor of the system.
	 */
	protected Executor primaryExecutor;

	/**
	 * The state factory for state-related computation.
	 */
	protected StateFactory stateFactory;

	/**
	 * The set of characters that are used to construct a number in a format
	 * string.
	 */
	protected Set<Character> numbers;

	protected LibraryExecutorLoader libExecutorLoader;

	/* **************************** Constructors *************************** */

	/**
	 * Creates a new instance of a library executor.
	 * 
	 * @param primaryExecutor
	 *            The executor for normal CIVL execution.
	 * @param output
	 *            The output stream to be used in the enabler.
	 * @param enablePrintf
	 *            If printing is enabled for the printf function.
	 * @param modelFactory
	 *            The model factory of the system.
	 * @param symbolicUtil
	 *            The symbolic utility used in the system.
	 * @param symbolicAnalyzer
	 *            The symbolic analyzer used in the system.
	 */
	public BaseLibraryExecutor(String name, Executor primaryExecutor,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer, CIVLConfiguration civlConfig,
			LibraryExecutorLoader libExecutorLoader,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, primaryExecutor.evaluator().universe(), symbolicUtil,
				symbolicAnalyzer, civlConfig, libEvaluatorLoader, modelFactory,
				primaryExecutor.errorLogger());
		this.primaryExecutor = primaryExecutor;
		this.evaluator = primaryExecutor.evaluator();
		this.stateFactory = evaluator.stateFactory();
		this.errorLogger = primaryExecutor.errorLogger();
		this.libExecutorLoader = libExecutorLoader;
		numbers = new HashSet<Character>(10);
		for (int i = 0; i < 10; i++) {
			numbers.add(Character.forDigit(i, 10));
		}
	}

	/* ************************* Protected Methods ************************* */

	protected State executeAssert(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source, CallOrSpawnStatement statement)
			throws UnsatisfiablePathConditionException {
		BooleanExpression assertValue = (BooleanExpression) argumentValues[0];
		Reasoner reasoner;
		ValidityResult valid;
		ResultType resultType;

		reasoner = universe.reasoner(state.getPathCondition());
		valid = reasoner.valid(assertValue);
		resultType = valid.getResultType();
		if (resultType != ResultType.YES) {
			StringBuilder message = new StringBuilder();
			Pair<State, String> messageResult = this.symbolicAnalyzer
					.expressionEvaluation(state, pid, arguments[0], false);
			String firstEvaluation, secondEvaluation, result;
			// StringBuffer inputVariableMap;

			state = messageResult.left;
			// inputVariableMap = symbolicAnalyzer
			// .inputVariablesToStringBuffer(state);
			// if (!inputVariableMap.toString().isEmpty()) {
			// message.append("\nInput variables:");
			// message.append(inputVariableMap);
			// }
			// message.append("\n\nContext: ");
			// message.append(this.symbolicAnalyzer.pathconditionToString(source,
			// state, "  ", reasoner.getReducedContext()));
			message.append("\nAssertion: ");
			message.append(arguments[0]);
			message.append("\n        -> ");
			// message.append(this.symbolicAnalyzer.statementEvaluation(state,
			// state, pid, statement));
			// // message.append(statement.toString());
			// message.append("\n   -> ");
			message.append(messageResult.right);
			firstEvaluation = messageResult.right;
			messageResult = this.symbolicAnalyzer.expressionEvaluation(state,
					pid, arguments[0], true);
			state = messageResult.left;
			secondEvaluation = messageResult.right;
			if (!firstEvaluation.equals(secondEvaluation)) {
				message.append("\n        -> ");
				message.append(secondEvaluation);
			}
			result = this.symbolicAnalyzer.symbolicExpressionToString(
					arguments[0].getSource(), state, null, assertValue)
					.toString();
			if (!secondEvaluation.equals(result)) {
				message.append("\n        -> ");
				message.append(result);
			}
			state = this.reportAssertionFailure(state, pid, process,
					resultType, message.toString(), arguments, argumentValues,
					source, assertValue, 1);
			state = state.setPathCondition(this.universe.and(
					state.getPathCondition(),
					(BooleanExpression) argumentValues[0]));
		}
		return state;
	}

	/**
	 * Executes the function call "$free(*void)": removes from the heap the
	 * object referred to by the given pointer.
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the process that the function call belongs to.
	 * @param arguments
	 *            The static representation of the arguments of the function
	 *            call.
	 * @param argumentValues
	 *            The dynamic representation of the arguments of the function
	 *            call.
	 * @param source
	 *            The source code element to be used for error report.
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	protected State executeFree(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression firstElementPointer = argumentValues[0];
		Pair<BooleanExpression, ResultType> checkPointer = symbolicAnalyzer
				.isDefinedPointer(state, firstElementPointer);

		if (checkPointer.right != ResultType.YES) {
			state = this.errorLogger
					.logError(source, state, process,
							symbolicAnalyzer.stateInformation(state),
							checkPointer.left, checkPointer.right,
							ErrorKind.MEMORY_MANAGE,
							"attempt to deallocate memory space through an undefined pointer");
			// dont report unsatisfiable path condition exception
		} else if (this.symbolicUtil.isNullPointer(firstElementPointer)) {
			// does nothing for null pointer.
		} else if (!this.symbolicUtil.isHeapPointer(firstElementPointer)
				|| !this.symbolicUtil.isMallocPointer(source,
						firstElementPointer)) {
			this.errorLogger.logSimpleError(
					source,
					state,
					process,
					symbolicAnalyzer.stateInformation(state),
					ErrorKind.MEMORY_MANAGE,
					"the argument of free "
							+ symbolicAnalyzer.symbolicExpressionToString(
									source, state,
									arguments[0].getExpressionType(),
									firstElementPointer)
							+ " is not a pointer returned by a memory "
							+ "management method");
		} else {
			Evaluation eval;
			SymbolicExpression heapObject = null;
			Pair<BooleanExpression, ResultType> checkDerefable = symbolicAnalyzer
					.isDerefablePointer(state, firstElementPointer);

			if (checkDerefable.right == ResultType.YES) {
				eval = this.evaluator.dereference(source, state, process, null,
						firstElementPointer, false);
				heapObject = eval.value;
				state = eval.state;
			}
			if (heapObject != null && heapObject.isNull()) {
				// the heap object has been deallocated
				this.errorLogger
						.logSimpleError(source, state, process,
								symbolicAnalyzer.stateInformation(state),
								ErrorKind.MEMORY_MANAGE,
								"attempt to deallocate an object that has been deallocated previously");
			} else {
				Pair<Integer, Integer> indexes;

				indexes = getMallocIndex(firstElementPointer);
				state = stateFactory.deallocate(state, firstElementPointer,
						modelFactory.getScopeId(source, universe.tupleRead(
								firstElementPointer, zeroObject)),
						indexes.left, indexes.right);
			}
		}
		return state;
	}

	/**
	 * A helper function for reporting runtime assertion failure. The helper
	 * function is aiming to be re-used by both execution implementations of
	 * $assert() and $assert_equal();
	 * 
	 * @author ziqing luo
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The string identifier of the process
	 * @param resultType
	 *            The {@link ResultType} of the failure assertion
	 * @param arguments
	 *            The expressions of the arguments
	 * @param argumentValues
	 *            The symbolic expressions of the arguments
	 * @param source
	 *            The CIVL source of the assertion statement
	 * @param claim
	 *            The boolean expression of the value of the assertion claim
	 * @param msgOffset
	 *            the start index in arguments list of the assertion failure
	 *            messages.
	 * @return the new state after reporting the assertion failure
	 * @throws UnsatisfiablePathConditionException
	 */
	protected State reportAssertionFailure(State state, int pid,
			String process, ResultType resultType, String message,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source, BooleanExpression claim, int msgOffset)
			throws UnsatisfiablePathConditionException {
		assert resultType != ResultType.YES;
		if (arguments.length > msgOffset) {
			// if (civlConfig.enablePrintf()) {
			Expression[] pArguments = Arrays.copyOfRange(arguments, msgOffset,
					arguments.length);
			SymbolicExpression[] pArgumentValues = Arrays.copyOfRange(
					argumentValues, msgOffset, argumentValues.length);

			state = this.primaryExecutor.execute_printf(source, state, pid,
					process, null, pArguments, pArgumentValues);
			civlConfig.out().println();
			// }
		}
		state = errorLogger.logError(source, state, process,
				this.symbolicAnalyzer.stateInformation(state), claim,
				resultType, ErrorKind.ASSERTION_VIOLATION, message);
		// errorLogger.logSimpleError(source, state, process,
		// this.symbolicAnalyzer.stateInformation(state),
		// ErrorKind.ASSERTION_VIOLATION, message);
		return state;
	}

	/**
	 * $exit terminates the calling process.
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The process ID of the process to be terminated.
	 * @return The state resulting from removing the specified process.
	 */
	protected State executeExit(State state, int pid) {
		int atomicPID = stateFactory.processInAtomic(state);

		if (atomicPID == pid) {
			state = stateFactory.releaseAtomicLock(state);
		}
		return stateFactory.terminateProcess(state, pid);
	}

	/* ************************** Private Methods ************************** */

	/**
	 * Obtains the field ID in the heap type via a heap-object pointer.
	 * 
	 * @param pointer
	 *            The heap-object pointer.
	 * @return The field ID in the heap type of the heap-object that the given
	 *         pointer refers to.
	 */
	private Pair<Integer, Integer> getMallocIndex(SymbolicExpression pointer) {
		// ref points to element 0 of an array:
		NTReferenceExpression ref = (NTReferenceExpression) symbolicUtil
				.getSymRef(pointer);
		// objectPointer points to array:
		ArrayElementReference objectPointer = (ArrayElementReference) ref
				.getParent();
		int mallocIndex = ((IntegerNumber) universe.extractNumber(objectPointer
				.getIndex())).intValue();
		// fieldPointer points to the field:
		TupleComponentReference fieldPointer = (TupleComponentReference) objectPointer
				.getParent();
		int mallocId = fieldPointer.getIndex().getInt();

		return new Pair<>(mallocId, mallocIndex);
	}
}
