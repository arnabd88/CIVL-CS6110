package edu.udel.cis.vsl.civl.library.civlc;

import java.math.BigInteger;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryExecutor;
import edu.udel.cis.vsl.civl.log.IF.CIVLExecutionException;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.Certainty;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.ModelConfiguration;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression.BINARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;

/**
 * Implementation of the execution for system functions declared civlc.h.
 * 
 * @author siegel
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class LibcivlcExecutor extends BaseLibraryExecutor implements
		LibraryExecutor {

	/* **************************** Constructors *************************** */

	/**
	 * Creates a new instance of the library executor for civlc.h.
	 * 
	 * @param name
	 *            The name of the library, which is concurrency.
	 * @param primaryExecutor
	 *            The executor for normal CIVL execution.
	 * @param modelFactory
	 *            The model factory of the system.
	 * @param symbolicUtil
	 *            The symbolic utility to be used.
	 * @param civlConfig
	 *            The CIVL configuration configured by the user.
	 */
	public LibcivlcExecutor(String name, Executor primaryExecutor,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer, CIVLConfiguration civlConfig,
			LibraryExecutorLoader libExecutorLoader,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, primaryExecutor, modelFactory, symbolicUtil,
				symbolicAnalyzer, civlConfig, libExecutorLoader,
				libEvaluatorLoader);
	}

	/* ******************** Methods from LibraryExecutor ******************* */

	@Override
	public State execute(State state, int pid, CallOrSpawnStatement statement,
			String functionName) throws UnsatisfiablePathConditionException {
		return executeWork(state, pid, statement, functionName);
	}

	/* ************************** Private Methods ************************** */

	/**
	 * Executes a system function call, updating the left hand side expression
	 * with the returned value if any.
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the process that the function call belongs to.
	 * @param call
	 *            The function call statement to be executed.
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeWork(State state, int pid, CallOrSpawnStatement call,
			String functionName) throws UnsatisfiablePathConditionException {
		Expression[] arguments;
		SymbolicExpression[] argumentValues;
		LHSExpression lhs;
		int numArgs;
		String process = state.getProcessState(pid).name() + "(id=" + pid + ")";

		numArgs = call.arguments().size();
		lhs = call.lhs();
		arguments = new Expression[numArgs];
		argumentValues = new SymbolicExpression[numArgs];
		for (int i = 0; i < numArgs; i++) {
			Evaluation eval;

			arguments[i] = call.arguments().get(i);
			eval = evaluator.evaluate(state, pid, arguments[i]);
			argumentValues[i] = eval.value;
			state = eval.state;
		}
		switch (functionName) {
		case "$assert":
			state = this.executeAssert(state, pid, process, arguments,
					argumentValues, call.getSource(), call);
			break;
		case "$assume":
			state = this.executeAssume(state, pid, process, arguments,
					argumentValues, call.getSource(), call);
			break;
		case "$choose_int_work":
			if (lhs != null)
				state = primaryExecutor.assign(state, pid, process, lhs,
						argumentValues[0]);
			break;
		case "$defined":
			state = executeDefined(state, pid, process, lhs, arguments,
					argumentValues, call.getSource(), call);
			break;
		case "$exit":// return immediately since no transitions needed after an
			// exit, because the process no longer exists.
			return executeExit(state, pid);
		case "$free":
		case "$int_iter_destroy":
			state = executeFree(state, pid, process, arguments, argumentValues,
					call.getSource());
			break;
		case "$int_iter_create":
			state = this.executeIntIterCreate(state, pid, process, lhs,
					arguments, argumentValues, call.getSource());
			break;
		case "$int_iter_hasNext":
			state = this.executeIntIterHasNext(state, pid, process, lhs,
					arguments, argumentValues, call.getSource());
			break;
		case "$int_iter_next":
			state = this.executeIntIterNext(state, pid, process, lhs,
					arguments, argumentValues, call.getSource());
			break;
		case "$pathCondition":
			state = this.executePathCondition(state, pid, process, arguments,
					argumentValues, call.getSource());
			break;
		case "$proc_defined":
			state = this.executeProcDefined(state, pid, process, lhs,
					arguments, argumentValues);
			break;
		case "$scope_defined":
			state = this.executeScopeDefined(state, pid, process, lhs,
					arguments, argumentValues);
			break;
		case "$wait":// return immediately since target location has been set.
			return executeWait(state, pid, arguments, argumentValues,
					call.getSource(), call.target());
		case "$waitall":
			return executeWaitAll(state, pid, arguments, argumentValues,
					call.getSource(), call.target());
		case "$set_default":
			state = executeSetDefault(state, pid, process, arguments,
					argumentValues, call.getSource());
			break;
		case "$apply":
			state = executeApply(state, pid, process, arguments,
					argumentValues, call.getSource());
			break;
		case "$next_time_count":
			state = this.executeNextTimeCount(state, pid, process, lhs,
					arguments, argumentValues);
			break;
		default:
			throw new CIVLInternalException("Unknown civlc function: " + name,
					call);
		}
		state = stateFactory.setLocation(state, pid, call.target(),
				call.lhs() != null);
		return state;
	}

	/* ************************** Private Methods ************************** */

	private State executePathCondition(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		if (this.civlConfig.enablePrintf())
			this.civlConfig.out().println(
					"path condition: "
							+ this.symbolicAnalyzer.symbolicExpressionToString(
									source, state, state.getPathCondition()));
		return state;
	}

	private State executeDefined(State state, int pid, String process,
			LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source,
			CallOrSpawnStatement call)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression pointer = argumentValues[0], result = trueValue;
		Evaluation eval = this.evaluator.dereference(arguments[0].getSource(),
				state, process, arguments[0], pointer, false);

		state = eval.state;
		if (eval.value.isNull()) {
			result = falseValue;
		}
		if (lhs != null)
			state = this.primaryExecutor.assign(state, pid, process, lhs,
					result);
		return state;
	}

	private State executeAssume(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source, CallOrSpawnStatement call) {
		BooleanExpression assumeValue = (BooleanExpression) argumentValues[0];
		BooleanExpression oldPathCondition, newPathCondition;

		oldPathCondition = state.getPathCondition();
		newPathCondition = universe.and(oldPathCondition, assumeValue);
		state = state.setPathCondition(newPathCondition);
		return state;
	}

	private State executeNextTimeCount(State state, int pid, String process,
			LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		Variable timeCountVar = this.modelFactory.timeCountVariable();
		NumericExpression timeCountValue = (NumericExpression) state.valueOf(
				pid, timeCountVar);

		state = stateFactory.setVariable(state, timeCountVar, pid,
				universe.add(timeCountValue, one));
		if (lhs != null)
			state = this.primaryExecutor.assign(state, pid, process, lhs,
					timeCountValue);
		return state;
	}

	/**
	 * <pre>
	 * applies the operation op on obj1 and obj2 and stores the result 
	 * void $apply(void *obj1, $operation op, void *obj2, void *result);
	 * </pre>
	 * 
	 * 
	 * @param state
	 * @param pid
	 * @param process
	 * @param arguments
	 * @param argumentValues
	 * @param source
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeApply(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		// TODO Auto-generated method stub
		SymbolicExpression obj1, obj2, result;
		Evaluation eval;
		int operator;

		eval = this.evaluator.dereference(arguments[0].getSource(), state,
				process, arguments[0], argumentValues[0], false);
		state = eval.state;
		obj1 = eval.value;
		eval = this.evaluator.dereference(arguments[2].getSource(), state,
				process, arguments[2], argumentValues[2], false);
		state = eval.state;
		obj2 = eval.value;
		operator = this.symbolicUtil.extractInt(arguments[1].getSource(),
				(NumericExpression) argumentValues[1]);
		result = this.applyCIVLOperator(state, process, obj1, obj2,
				this.translateOperator(operator), source);
		state = this.primaryExecutor.assign(source, state, process,
				argumentValues[3], result);
		return state;
	}

	/**
	 * <pre>
	 * updates the leaf nodes of a status variable to the default value 0
	 * 
	 * void $set_default(void *status);
	 * </pre>
	 * 
	 * @param state
	 * @param pid
	 * @param process
	 * @param arguments
	 * @param argumentValues
	 * @param source
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeSetDefault(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		// TODO Auto-generated method stub
		CIVLType objectTypeByPointer = symbolicAnalyzer.typeOfObjByPointer(
				arguments[0].getSource(), state, argumentValues[0]);
		SymbolicExpression value;

		// TODO assert objectTypeByPointer.isScalarType()
		if (objectTypeByPointer.isBoolType())
			value = this.falseValue;
		else if (objectTypeByPointer.isIntegerType())
			value = this.zero;
		else if (objectTypeByPointer.isRealType())
			value = universe.rational(0);
		else if (objectTypeByPointer.isCharType())
			value = universe.character((char) 0);
		else if (objectTypeByPointer.isPointerType())
			value = symbolicUtil.nullPointer();
		else
			throw new CIVLUnimplementedFeatureException("Argument of "
					+ objectTypeByPointer + " type for $set_default()", source);
		state = this.primaryExecutor.assign(source, state, process,
				argumentValues[0], value);
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
	private State executeExit(State state, int pid) {
		int atomicPID = stateFactory.processInAtomic(state);

		if (atomicPID == pid) {
			state = stateFactory.releaseAtomicLock(state);
		}
		return stateFactory.terminateProcess(state, pid);
	}

	/**
	 * Creates a new iterator for an array of integers, and returns the handle
	 * of the iterator. The new object will be allocated in the given scope.<br>
	 * <code>$int_iter $int_iter_create($scope scope, int *array, int
	 * size);</code>
	 * 
	 * <code>
	 * typedef struct __int_iter__ {<br>
	 * &nbsp;&nbsp;int size;<br>
	 * &nbsp;&nbsp;int content[];<br>
	 * &nbsp;&nbsp;int index; //initialized as 0<br>
	 * } $int_iter;
	 * </code>
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the process that the function call belongs to.
	 * @param lhs
	 *            The left hand side expression of the call, which is to be
	 *            assigned with the returned value of the function call. If NULL
	 *            then no assignment happens.
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
	private State executeIntIterCreate(State state, int pid, String process,
			LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression intIterObj;
		SymbolicExpression size = argumentValues[2];
		SymbolicExpression currentIndex = universe.integer(0);
		SymbolicExpression scope = argumentValues[0];
		Expression scopeExpression = arguments[0];
		SymbolicExpression arrayPointer = argumentValues[1];
		Expression arrayPointerExpression = arguments[1];
		SymbolicExpression intArray;
		LinkedList<SymbolicExpression> intArrayComponents = new LinkedList<>();
		List<SymbolicExpression> intIterComponents = new LinkedList<>();
		int int_size;
		CIVLType intIterType = typeFactory
				.systemType(ModelConfiguration.INT_ITER_TYPE);
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		IntegerNumber number_size = (IntegerNumber) reasoner
				.extractNumber((NumericExpression) size);
		Evaluation eval = evaluator.dereference(source, state, process,
				arguments[1], arrayPointer, false);
		CIVLSource arrayPointerSource = arrayPointerExpression.getSource();

		state = eval.state;
		if (number_size != null)
			int_size = number_size.intValue();
		else
			throw new CIVLInternalException(
					"Cannot extract concrete int value for gbarrier size",
					arguments[1]);
		for (int i = 0; i < int_size; i++) {
			BinaryExpression pointerAdditionExpression = modelFactory
					.binaryExpression(arrayPointerExpression.getSource(),
							BINARY_OPERATOR.POINTER_ADD,
							arrayPointerExpression, modelFactory
									.integerLiteralExpression(
											arrayPointerExpression.getSource(),
											BigInteger.valueOf(i)));
			SymbolicExpression arrayElePointer;

			eval = evaluator.pointerAdd(state, pid, process,
					pointerAdditionExpression, arrayPointer,
					universe.integer(i));
			state = eval.state;
			arrayElePointer = eval.value;
			eval = evaluator.dereference(arrayPointerSource, state, process,
					pointerAdditionExpression, arrayElePointer, false);
			state = eval.state;
			intArrayComponents.add(eval.value);
		}
		intArray = universe.array(
				typeFactory.integerType().getDynamicType(universe),
				intArrayComponents);
		intIterComponents.add(size);
		intIterComponents.add(intArray);
		intIterComponents.add(currentIndex);
		intIterObj = universe.tuple(
				(SymbolicTupleType) intIterType.getDynamicType(universe),
				intIterComponents);
		state = primaryExecutor.malloc(source, state, pid, process, lhs,
				scopeExpression, scope, intIterType, intIterObj);
		return state;
	}

	/**
	 * Tells whether the integer iterator has any more elements.
	 * <code>_Bool $int_iter_hasNext($int_iter iter);</code>
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the process that the function call belongs to.
	 * @param lhs
	 *            The left hand side expression of the call, which is to be
	 *            assigned with the returned value of the function call. If NULL
	 *            then no assignment happens.
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
	private State executeIntIterHasNext(State state, int pid, String process,
			LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression iterHandle = argumentValues[0];
		SymbolicExpression iterObj;
		CIVLSource civlsource = arguments[0].getSource();
		Evaluation eval;
		NumericExpression size, index;
		SymbolicExpression hasNext;

		eval = evaluator.dereference(civlsource, state, process, arguments[0],
				iterHandle, false);
		state = eval.state;
		iterObj = eval.value;
		size = (NumericExpression) universe.tupleRead(iterObj, zeroObject);
		index = (NumericExpression) universe.tupleRead(iterObj, twoObject);
		hasNext = universe.lessThan(index, size);
		if (lhs != null) {
			state = primaryExecutor.assign(state, pid, process, lhs, hasNext);
		}
		return state;
	}

	/*
	 * Tells whether the integer iterator has any more elements _Bool
	 * $int_iter_hasNext($int_iter iter);
	 * 
	 * Returns the next element in the iterator (and updates the iterator) int
	 * $int_iter_next($int_iter iter);
	 * 
	 * Creates a new iterator for an array of integers, and returns the handle
	 * of the iterator. $int_iter $int_iter_create($scope scope, int *array, int
	 * size);
	 */

	/**
	 * Returns the next element in the iterator (and updates the iterator).
	 * <code>int $int_iter_next($int_iter iter);</code>
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the process that the function call belongs to.
	 * @param lhs
	 *            The left hand side expression of the call, which is to be
	 *            assigned with the returned value of the function call. If NULL
	 *            then no assignment happens.
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
	private State executeIntIterNext(State state, int pid, String process,
			LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression iterHandle = argumentValues[0];
		SymbolicExpression array;
		SymbolicExpression iterObj;
		CIVLSource civlsource = arguments[0].getSource();
		Evaluation eval;
		NumericExpression index;
		SymbolicExpression nextInt;

		eval = evaluator.dereference(civlsource, state, process, arguments[0],
				iterHandle, false);
		state = eval.state;
		iterObj = eval.value;
		array = universe.tupleRead(iterObj, oneObject);
		index = (NumericExpression) universe.tupleRead(iterObj, twoObject);
		nextInt = universe.arrayRead(array, index);
		if (lhs != null) {
			state = primaryExecutor.assign(state, pid, process, lhs, nextInt);
		}
		// updates iterator object
		index = universe.add(index, one);
		iterObj = universe.tupleWrite(iterObj, twoObject, index);
		state = primaryExecutor.assign(source, state, process, iterHandle,
				iterObj);
		return state;
	}

	/**
	 * Checks if a process reference is defined, i.e., its id is non-negative.
	 * 
	 * @param state
	 *            The state where the checking happens.
	 * @param pid
	 *            The ID of the process that this computation belongs to.
	 * @param lhs
	 *            The left hand side expression of this function call.
	 * @param arguments
	 *            The static arguments of the function call.
	 * @param argumentValues
	 *            The symbolic values of the arguments of the function call
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeProcDefined(State state, int pid, String process,
			LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		int procValue = modelFactory.getProcessId(arguments[0].getSource(),
				argumentValues[0]);
		SymbolicExpression result = modelFactory.isPocessIdDefined(procValue) ? trueValue
				: falseValue;

		if (lhs != null)
			state = primaryExecutor.assign(state, pid, process, lhs, result);
		return state;
	}

	/**
	 * Checks if a scope reference is defined, i.e., its id is non-negative.
	 * 
	 * @param state
	 *            The state where the checking happens.
	 * @param pid
	 *            The ID of the process that this computation belongs to.
	 * @param lhs
	 *            The left hand side expression of this function call.
	 * @param arguments
	 *            The static arguments of the function call.
	 * @param argumentValues
	 *            The symbolic values of the arguments of the function call
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeScopeDefined(State state, int pid, String process,
			LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		int scopeValue = modelFactory.getScopeId(arguments[0].getSource(),
				argumentValues[0]);
		SymbolicExpression result = modelFactory.isScopeIdDefined(scopeValue) ? trueValue
				: falseValue;

		if (lhs != null)
			state = primaryExecutor.assign(state, pid, process, lhs, result);
		return state;
	}

	/**
	 * Executes the $wait system function call. Only enabled when the waited
	 * process has terminated.
	 * 
	 * * @param state The current state.
	 * 
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
	 * @param target
	 *            The target location of the wait function call.
	 * @return The new state after executing the function call.
	 * @return
	 */
	private State executeWait(State state, int pid, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source,
			Location target) {
		SymbolicExpression procVal = argumentValues[0];
		int joinedPid = modelFactory.getProcessId(arguments[0].getSource(),
				procVal);

		state = stateFactory.setLocation(state, pid, target);
		if (!modelFactory.isPocessIdDefined(joinedPid)
				|| modelFactory.isProcessIdNull(joinedPid))
			return state;
		state = stateFactory.removeProcess(state, joinedPid);
		return state;
	}

	private State executeWaitAll(State state, int pid, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source,
			Location target) throws UnsatisfiablePathConditionException {
		SymbolicExpression procsPointer = argumentValues[0];
		SymbolicExpression numOfProcs = argumentValues[1];
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		IntegerNumber number_nprocs = (IntegerNumber) reasoner
				.extractNumber((NumericExpression) numOfProcs);
		String process = state.getProcessState(pid).name() + "(id=" + pid + ")";

		if (number_nprocs == null) {
			CIVLExecutionException err = new CIVLExecutionException(
					ErrorKind.OTHER, Certainty.PROVEABLE, process,
					"The number of processes for $waitall "
							+ "needs a concrete value.",
					symbolicAnalyzer.stateInformation(state),
					arguments[1].getSource());

			this.errorLogger.reportError(err);
		} else {
			int numOfProcs_int = number_nprocs.intValue();
			BinaryExpression pointerAdd;
			CIVLSource procsSource = arguments[0].getSource();
			Evaluation eval;

			for (int i = 0; i < numOfProcs_int; i++) {
				Expression offSet = modelFactory.integerLiteralExpression(
						procsSource, BigInteger.valueOf(i));
				NumericExpression offSetV = universe.integer(i);
				SymbolicExpression procPointer, proc;
				int pidValue;

				pointerAdd = modelFactory.binaryExpression(procsSource,
						BINARY_OPERATOR.POINTER_ADD, arguments[0], offSet);
				eval = evaluator.pointerAdd(state, pid, process, pointerAdd,
						procsPointer, offSetV);
				procPointer = eval.value;
				state = eval.state;
				eval = evaluator.dereference(procsSource, state, process,
						pointerAdd, procPointer, false);
				proc = eval.value;
				state = eval.state;
				pidValue = modelFactory.getProcessId(procsSource, proc);
				if (!modelFactory.isProcessIdNull(pidValue)
						&& modelFactory.isPocessIdDefined(pidValue))
					state = stateFactory.removeProcess(state, pidValue);
			}
			state = stateFactory.setLocation(state, pid, target);
		}
		return state;
	}

}
