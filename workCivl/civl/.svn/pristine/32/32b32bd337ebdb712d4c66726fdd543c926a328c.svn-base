package edu.udel.cis.vsl.civl.library.comm;

import java.util.Arrays;
import java.util.LinkedList;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryExecutor;
import edu.udel.cis.vsl.civl.log.IF.CIVLExecutionException;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.Certainty;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.ModelConfiguration;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLBundleType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class LibcommExecutor extends BaseLibraryExecutor implements
		LibraryExecutor {

	/* **************************** Constructors *************************** */

	public LibcommExecutor(String name, Executor primaryExecutor,
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
	public State execute(State state, int pid, CallOrSpawnStatement statement)
			throws UnsatisfiablePathConditionException {
		return executeWork(state, pid, statement);
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
	private State executeWork(State state, int pid, CallOrSpawnStatement call)
			throws UnsatisfiablePathConditionException {
		Identifier name;
		Expression[] arguments;
		SymbolicExpression[] argumentValues;
		LHSExpression lhs;
		int numArgs;
		String process = state.getProcessState(pid).name() + "(id=" + pid + ")";

		numArgs = call.arguments().size();
		name = call.function().name();
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
		switch (name.name()) {
		case "$comm_create":
			state = this.executeCommCreate(state, pid, process, lhs, arguments,
					argumentValues);
			break;
		case "$comm_defined":
			state = this.executeCommDefined(state, pid, process, lhs,
					arguments, argumentValues);
			break;
		case "$comm_dequeue":
			state = executeCommDequeue(state, pid, process, lhs, arguments,
					argumentValues);
			break;
		case "$comm_dequeue_work":
			state = executeCommDequeue(state, pid, process, lhs, arguments,
					argumentValues);
			break;
		case "$comm_enqueue":
			state = executeCommEnqueue(state, pid, process, arguments,
					argumentValues);
			break;
		case "$comm_seek":
			state = this.executeCommSeek(state, pid, process, lhs, arguments,
					argumentValues);
			break;
		case "$comm_probe":
			state = this.executeCommProbe(state, pid, process, lhs, arguments,
					argumentValues);
			break;
		case "$comm_size":
			state = this.executeCommSize(state, pid, process, lhs, arguments,
					argumentValues);
			break;
		case "$comm_destroy":
			state = executeFree(state, pid, process, arguments, argumentValues,
					call.getSource());
			break;
		case "$gcomm_destroy":
			state = this.executeGcommDestroy(state, pid, process, lhs,
					arguments, argumentValues, call.getSource());
			break;
		case "$gcomm_create":
			state = executeGcommCreate(state, pid, process, lhs, arguments,
					argumentValues, call.getSource());
			break;
		case "$gcomm_defined":
			state = this.executeGcommDefined(state, pid, process, lhs,
					arguments, argumentValues);
			break;
		}
		state = stateFactory.setLocation(state, pid, call.target(),
				call.lhs() != null);
		return state;
	}

	/**
	 * Creates a new local communicator object and returns a handle to it. The
	 * new communicator will be affiliated with the specified global
	 * communicator. This local communicator handle will be used as an argument
	 * in most message-passing functions. The place must be in [0,size-1] and
	 * specifies the place in the global communication universe that will be
	 * occupied by the local communicator. The local communicator handle may be
	 * used by more than one process, but all of those processes will be viewed
	 * as occupying the same place. Only one call to $comm_create may occur for
	 * each gcomm-place pair. The new object will be allocated in the given
	 * scope.
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
	private State executeCommCreate(State state, int pid, String process,
			LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression scope = argumentValues[0];
		Expression scopeExpression = arguments[0];
		SymbolicExpression gcommHandle = argumentValues[1];
		SymbolicExpression place = argumentValues[2];
		SymbolicExpression gcomm;
		SymbolicExpression comm;
		SymbolicExpression isInitArray;
		LinkedList<SymbolicExpression> commComponents = new LinkedList<SymbolicExpression>();
		CIVLSource civlsource = arguments[0].getSource();
		CIVLType commType = modelFactory
				.getSystemType(ModelConfiguration.COMM_TYPE);
		Evaluation eval;

		eval = this.evaluator.dereference(civlsource, state, process,
				gcommHandle, false);
		state = eval.state;
		gcomm = eval.value;
		isInitArray = universe.tupleRead(gcomm, oneObject);
		// TODO report an error if the place has already been taken by other
		// processes.
		assert universe.arrayRead(isInitArray, (NumericExpression) place)
				.equals(universe.bool(false));
		// TODO report an error if the place exceeds the size of the
		// communicator
		isInitArray = universe.arrayWrite(isInitArray,
				(NumericExpression) place, universe.bool(true));
		gcomm = universe.tupleWrite(gcomm, oneObject, isInitArray);
		state = this.primaryExecutor.assign(civlsource, state, process,
				gcommHandle, gcomm);
		// builds comm
		commComponents.add(place);
		commComponents.add(gcommHandle);
		comm = universe.tuple(
				(SymbolicTupleType) commType.getDynamicType(universe),
				commComponents);
		state = this.primaryExecutor.malloc(civlsource, state, pid, process,
				lhs, scopeExpression, scope, commType, comm);
		return state;
	}

	/**
	 * Checks if a $comm object is defined, i.e., it doesn't point to the heap
	 * of an invalid scope, implementing the function $comm_defined($comm comm).
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
	private State executeCommDefined(State state, int pid, String process,
			LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		boolean isValid = symbolicUtil.isValidPointer(argumentValues[0]);
		SymbolicExpression result = isValid ? this.trueValue : this.falseValue;

		if (lhs != null)
			state = primaryExecutor.assign(state, pid, process, lhs, result);
		return state;
	}

	/**
	 * Finds the first matching message, removes it from the communicator, and
	 * returns the message
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
	private State executeCommDequeue(State state, int pid, String process,
			LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		CIVLSource civlsource = state.getProcessState(pid).getLocation()
				.getSource();
		SymbolicExpression message = null;
		SymbolicExpression commHandle = argumentValues[0];
		SymbolicExpression comm;
		SymbolicExpression gcommHandle;
		SymbolicExpression gcomm;
		NumericExpression source = (NumericExpression) argumentValues[1];
		NumericExpression tag = (NumericExpression) argumentValues[2];
		NumericExpression dest;
		SymbolicExpression buf;
		SymbolicExpression bufRow = null;
		SymbolicExpression queue = null;
		NumericExpression queueLength = null;
		SymbolicExpression messages = null;
		Evaluation eval;
		int msgIdx;

		eval = evaluator.dereference(civlsource, state, process, commHandle,
				false);
		state = eval.state;
		comm = eval.value;
		gcommHandle = universe.tupleRead(comm, oneObject);
		eval = evaluator.dereference(civlsource, state, process, gcommHandle,
				false);
		state = eval.state;
		gcomm = eval.value;
		buf = universe.tupleRead(gcomm, universe.intObject(2));
		dest = (NumericExpression) universe.tupleRead(comm, zeroObject);
		bufRow = universe.arrayRead(buf, source);
		queue = universe.arrayRead(bufRow, dest);
		queueLength = (NumericExpression) universe.tupleRead(queue, zeroObject);
		messages = universe.tupleRead(queue, oneObject);
		msgIdx = this.getMatchedMsgIdx(state, pid, messages, queueLength, tag,
				civlsource);
		if (msgIdx == -1)
			throw new CIVLExecutionException(ErrorKind.INTERNAL,
					Certainty.CONCRETE, state.getProcessState(pid).name(),
					"Message dequeue fails", civlsource);
		message = universe.arrayRead(messages, universe.integer(msgIdx));
		messages = universe.removeElementAt(messages, msgIdx);
		queueLength = universe.subtract(queueLength, one);
		queue = universe.tupleWrite(queue, zeroObject, queueLength);
		queue = universe.tupleWrite(queue, oneObject, messages);
		bufRow = universe.arrayWrite(bufRow, dest, queue);
		buf = universe.arrayWrite(buf, source, bufRow);
		gcomm = universe.tupleWrite(gcomm, universe.intObject(2), buf);
		state = this.primaryExecutor.assign(civlsource, state, process,
				gcommHandle, gcomm);
		if (lhs != null) {
			state = this.primaryExecutor.assign(state, pid, process, lhs,
					message);
		}
		return state;
	}

	/**
	 * Adds the message to the appropriate message queue in the communication
	 * universe specified by the comm. The source of the message must equal the
	 * place of the comm.
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
	private State executeCommEnqueue(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		CIVLSource civlsource = arguments[0].getSource();
		SymbolicExpression commHandle = argumentValues[0];
		SymbolicExpression newMessage = argumentValues[1];
		SymbolicExpression comm;
		SymbolicExpression gcommHandle;
		SymbolicExpression gcomm;
		SymbolicExpression source;
		SymbolicExpression dest;
		SymbolicExpression buf;
		SymbolicExpression bufRow;
		SymbolicExpression queue;
		SymbolicExpression queueLength;
		SymbolicExpression messages;
		Evaluation eval;
		int int_queueLength;

		eval = evaluator.dereference(civlsource, state, process, commHandle,
				false);
		state = eval.state;
		comm = eval.value;
		gcommHandle = universe.tupleRead(comm, oneObject);
		eval = evaluator.dereference(civlsource, state, process, gcommHandle,
				false);
		state = eval.state;
		gcomm = eval.value;
		buf = universe.tupleRead(gcomm, universe.intObject(2));
		// TODO checks if source is equal to the place of comm.
		source = universe.tupleRead(newMessage, zeroObject);
		dest = universe.tupleRead(newMessage, oneObject);
		bufRow = universe.arrayRead(buf, (NumericExpression) source);
		queue = universe.arrayRead(bufRow, (NumericExpression) dest);
		queueLength = universe.tupleRead(queue, zeroObject);
		messages = universe.tupleRead(queue, oneObject);
		messages = universe.append(messages, newMessage);
		int_queueLength = symbolicUtil.extractInt(civlsource,
				(NumericExpression) queueLength);
		int_queueLength++;
		queueLength = universe.integer(int_queueLength);
		queue = universe.tupleWrite(queue, zeroObject, queueLength);
		queue = universe.tupleWrite(queue, oneObject, messages);
		bufRow = universe.arrayWrite(bufRow, (NumericExpression) dest, queue);
		buf = universe.arrayWrite(buf, (NumericExpression) source, bufRow);
		gcomm = universe.tupleWrite(gcomm, universe.intObject(2), buf);
		state = this.primaryExecutor.assign(civlsource, state, process,
				gcommHandle, gcomm);
		return state;
	}

	/**
	 * Returns true iff a matching message exists in the communication universe
	 * specified by the comm. A message matches the arguments if the destination
	 * of the message is the place of the comm, and the sources and tags match.
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
	private State executeCommProbe(State state, int pid, String process,
			LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression commHandle = argumentValues[0];
		SymbolicExpression comm;
		SymbolicExpression gcommHandle;
		SymbolicExpression gcomm;
		NumericExpression source = (NumericExpression) argumentValues[1];
		SymbolicExpression tag = argumentValues[2];
		NumericExpression dest;
		SymbolicExpression queue, queueLength, messages;
		int msgIdx = -1;
		boolean isFind = false;
		CIVLSource civlsource = state.getProcessState(pid).getLocation()
				.getSource();
		Evaluation eval;

		eval = evaluator.dereference(civlsource, state, process, commHandle,
				false);
		state = eval.state;
		comm = eval.value;
		gcommHandle = universe.tupleRead(comm, oneObject);
		eval = evaluator.dereference(civlsource, state, process, gcommHandle,
				false);
		state = eval.state;
		gcomm = eval.value;
		dest = (NumericExpression) universe.tupleRead(comm, zeroObject);
		queue = universe.arrayRead(universe.arrayRead(
				universe.tupleRead(gcomm, twoObject), source), dest);
		queueLength = universe.tupleRead(queue, zeroObject);
		messages = universe.tupleRead(queue, oneObject);
		msgIdx = this.getMatchedMsgIdx(state, pid, messages, queueLength, tag,
				civlsource);
		if (msgIdx >= 0)
			isFind = true;
		if (lhs != null) {
			state = this.stateFactory.setVariable(state,
					((VariableExpression) lhs).variable(), pid,
					universe.bool(isFind));
		}
		return state;
	}

	/**
	 * Finds the first matching message and returns it without modifying the
	 * communication universe. If no matching message exists, returns a message
	 * with source, dest, and tag all negative.
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
	private State executeCommSeek(State state, int pid, String process,
			LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression commHandle = argumentValues[0];
		SymbolicExpression comm;
		SymbolicExpression gcommHandle;
		SymbolicExpression gcomm;
		NumericExpression source = (NumericExpression) argumentValues[1];
		NumericExpression dest;
		SymbolicExpression tag = argumentValues[2];
		SymbolicExpression message, messages, queue, queueLength;
		CIVLSource civlsource = state.getProcessState(pid).getLocation()
				.getSource();
		Evaluation eval;
		int msgIdx = -1;

		eval = evaluator.dereference(civlsource, state, process, commHandle,
				false);
		state = eval.state;
		comm = eval.value;
		gcommHandle = universe.tupleRead(comm, oneObject);
		eval = evaluator.dereference(civlsource, state, process, gcommHandle,
				false);
		state = eval.state;
		gcomm = eval.value;
		dest = (NumericExpression) universe.tupleRead(comm, zeroObject);
		queue = universe.arrayRead(universe.arrayRead(
				universe.tupleRead(gcomm, twoObject), source), dest);
		queueLength = universe.tupleRead(queue, zeroObject);
		messages = universe.tupleRead(queue, oneObject);
		msgIdx = this.getMatchedMsgIdx(state, pid, messages, queueLength, tag,
				civlsource);
		if (msgIdx == -1)
			message = this.getEmptyMessage(state);
		else
			message = universe.arrayRead(messages, universe.integer(msgIdx));
		if (lhs != null) {
			// state = this.stateFactory.setVariable(state,
			// ((VariableExpression) lhs).variable(), pid, message);
			state = primaryExecutor.assign(state, pid, process, lhs, message);
		}
		return state;
	}

	/**
	 * Returns the size (number of places) in the global communicator associated
	 * to the given comm.
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
	private State executeCommSize(State state, int pid, String process,
			LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression commHandle = argumentValues[0];
		SymbolicExpression comm;
		SymbolicExpression gcommHandle;
		SymbolicExpression gcomm;
		SymbolicExpression nprocs;
		CIVLSource civlsource = arguments[0].getSource();
		Evaluation eval;

		eval = evaluator.dereference(civlsource, state, process, commHandle,
				false);
		state = eval.state;
		comm = eval.value;
		gcommHandle = universe.tupleRead(comm, oneObject);
		eval = evaluator.dereference(civlsource, state, process, gcommHandle,
				false);
		state = eval.state;
		gcomm = eval.value;
		nprocs = universe.tupleRead(gcomm, zeroObject);
		if (lhs != null) {
			state = this.primaryExecutor.assign(state, pid, process, lhs,
					nprocs);
		}
		return state;
	}

	/**
	 * Creates a new global communicator object and returns a handle to it. The
	 * global communicator will have size communication places. The global
	 * communicator defines a communication "universe" and encompasses message
	 * buffers and all other components of the state associated to
	 * message-passing. The new object will be allocated in the given scope.
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
	private State executeGcommCreate(State state, int pid, String process,
			LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression gcomm;
		NumericExpression nprocs = (NumericExpression) argumentValues[1];
		SymbolicExpression scope = argumentValues[0];
		Expression scopeExpression = arguments[0];
		SymbolicExpression isInit;
		SymbolicExpression isInitArray;
		SymbolicExpression buf;
		SymbolicExpression bufRow;
		SymbolicExpression queueLength = universe.integer(0);
		SymbolicExpression emptyQueue;
		SymbolicExpression emptyMessages;
		CIVLType queueType = model.queueType();
		CIVLType messageType = model.mesageType();
		CIVLType gcommType = modelFactory
				.getSystemType(ModelConfiguration.GCOMM_TYPE);
		SymbolicType dynamicQueueType = queueType.getDynamicType(universe);
		SymbolicType dynamicMessageType = messageType.getDynamicType(universe);
		BooleanExpression context = state.getPathCondition();

		isInit = universe.bool(false);
		emptyMessages = universe.array(dynamicMessageType,
				new LinkedList<SymbolicExpression>());
		assert dynamicQueueType instanceof SymbolicTupleType;
		emptyQueue = universe.tuple((SymbolicTupleType) dynamicQueueType,
				Arrays.asList(queueLength, emptyMessages));
		isInitArray = symbolicUtil.newArray(context, isInit.type(), nprocs,
				isInit);
		bufRow = symbolicUtil.newArray(context, emptyQueue.type(), nprocs,
				emptyQueue);
		buf = symbolicUtil.newArray(context, bufRow.type(), nprocs, bufRow);
		gcomm = universe.tuple(
				(SymbolicTupleType) gcommType.getDynamicType(universe),
				Arrays.asList(nprocs, isInitArray, buf));
		state = primaryExecutor.malloc(source, state, pid, process, lhs,
				scopeExpression, scope, gcommType, gcomm);
		return state;
	}

	/**
	 * Checks if a $gcomm object is defined, i.e., it doesn't point to the heap
	 * of an invalid scope, implementing the function $gcomm_defined($gcomm
	 * gcomm).
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
	private State executeGcommDefined(State state, int pid, String process,
			LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		boolean isValid = symbolicUtil.isValidPointer(argumentValues[0]);
		SymbolicExpression result = isValid ? this.trueValue : this.falseValue;

		if (lhs != null)
			state = primaryExecutor.assign(state, pid, process, lhs, result);
		return state;
	}

	/**
	 * Free the gcomm object and check if there is any message still remaining
	 * the message buffer
	 * 
	 * @param state
	 *            the current state
	 * @param pid
	 *            the PID of the process
	 * @param process
	 *            the identifier of the process
	 * @param lhs
	 *            the left hand side expression
	 * @param arguments
	 *            expressions of the arguments
	 * @param argumentValues
	 *            symbolic expressions of the arguments
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeGcommDestroy(State state, int pid, String process,
			LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		Expression nprocExpr;
		Expression gcommHandleExpr = arguments[0];
		Expression gcommExpr;
		SymbolicExpression gcommHandle;
		SymbolicExpression gcomm;
		NumericExpression nprocs;
		SymbolicExpression buf;
		SymbolicExpression queues;
		int nprocs_int;
		Evaluation eval;

		gcommHandle = argumentValues[0];
		eval = evaluator.dereference(arguments[0].getSource(), state, process,
				gcommHandle, false);
		state = eval.state;
		gcomm = eval.value;
		nprocs = (NumericExpression) universe.tupleRead(gcomm, zeroObject);
		gcommExpr = modelFactory.dereferenceExpression(
				gcommHandleExpr.getSource(), gcommHandleExpr);
		nprocExpr = modelFactory.dotExpression(gcommExpr.getSource(),
				gcommExpr, 0);
		nprocs_int = symbolicUtil.extractInt(nprocExpr.getSource(), nprocs);
		buf = universe.tupleRead(gcomm, twoObject);
		for (int i = 0; i < nprocs_int; i++) {
			Reasoner reasoner = universe.reasoner(state.getPathCondition());

			queues = universe.arrayRead(buf, universe.integer(i));
			for (int j = 0; j < nprocs_int; j++) {
				SymbolicExpression queue;
				NumericExpression queueLength;
				BooleanExpression claim;
				ResultType resultType;

				queue = universe.arrayRead(queues, universe.integer(j));
				queueLength = (NumericExpression) universe.tupleRead(queue,
						zeroObject);
				claim = universe.lessThan(zero, queueLength);
				resultType = reasoner.valid(claim).getResultType();
				if (!resultType.equals(ResultType.NO)) {
					this.errorLogger
							.logError(
									source,
									state,
									process,
									symbolicAnalyzer.stateToString(state),
									claim,
									resultType,
									ErrorKind.MEMORY_LEAK,
									"There is at least one message still remaing in channel["
											+ i
											+ "]["
											+ j
											+ "] of the communicator referenced by "
											+ gcommHandleExpr
											+ " when the commmunicator is going to be destroied");
				}
			}
		}
		state = this.executeFree(state, pid, process, arguments,
				argumentValues, source);
		return state;
	}

	/**
	 * Read matched message index from the given messages array. Here
	 * "matched message" means if the given tag is wild card tag, then read the
	 * first message inside the messages array, otherwise the tag should be a
	 * specific tag then read the first message has the same tag inside the
	 * messages array.
	 * 
	 * Other cases like failure of finding a matched message or the tag is
	 * neither a wild card tag nor a valid specific tag will be an execution
	 * exception.
	 * 
	 * @param state
	 *            The current state which emanating the transition being
	 *            executed right now
	 * @param pid
	 *            The pid of the process
	 * @param messagesArray
	 *            The given messages array
	 * @param tag
	 *            The given message tag
	 * @param civlsource
	 * @return The index of a matched message in the given array
	 * @throws UnsatisfiablePathConditionException
	 */
	private int getMatchedMsgIdx(State state, int pid,
			SymbolicExpression messagesArray, SymbolicExpression queueLength,
			SymbolicExpression tag, CIVLSource civlsource)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression message = null;
		NumericExpression numericQueueLength = (NumericExpression) queueLength;
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		BooleanExpression isAnyTag = universe.equals(universe.integer(-2), tag);
		BooleanExpression isSpecTag = universe.lessThanEquals(zero,
				(NumericExpression) tag);
		int msgIndex = -1;

		// specific tag
		if (reasoner.isValid(isSpecTag)) {
			NumericExpression iter = zero;
			BooleanExpression iterQueueLengthClaim = universe.lessThan(iter,
					(NumericExpression) queueLength);

			while (reasoner.isValid(iterQueueLengthClaim)) {
				BooleanExpression isTagMatched;

				message = universe.arrayRead(messagesArray, iter);
				isTagMatched = universe
						.equals(universe.tupleRead(message,
								universe.intObject(2)), tag);
				if (reasoner.isValid(isTagMatched)) {
					msgIndex = symbolicUtil.extractInt(null, iter);
					break;
				}
				iter = universe.add(iter, one);
				iterQueueLengthClaim = universe.lessThan(iter,
						numericQueueLength);
			}
		}
		// wild card tag
		else if (reasoner.isValid(isAnyTag)) {
			BooleanExpression queueGTzeroClaim = universe.lessThan(zero,
					numericQueueLength);

			if (reasoner.isValid(queueGTzeroClaim))
				msgIndex = 0;

		}
		// Exception
		else {
			throw new CIVLExecutionException(ErrorKind.INTERNAL,
					Certainty.CONCRETE, state.getProcessState(pid).name(),
					"Unexpected arguments", civlsource);
		}
		return msgIndex;
	}

	private SymbolicExpression getEmptyMessage(State state) {
		SymbolicExpression message;
		CIVLType messageType = model.mesageType();
		CIVLBundleType bundleType = modelFactory.bundleType();
		LinkedList<SymbolicExpression> emptyMessageComponents = new LinkedList<SymbolicExpression>();
		StringObject name;
		SymbolicExpression bundle;

		name = universe.stringObject("X_s" + -1 + "v" + -1);
		bundle = universe.symbolicConstant(name,
				bundleType.getDynamicType(universe));
		emptyMessageComponents.add(universe.integer(-1));
		emptyMessageComponents.add(universe.integer(-1));
		emptyMessageComponents.add(universe.integer(-1));
		emptyMessageComponents.add(bundle);
		emptyMessageComponents.add(universe.integer(-1));
		message = this.universe.tuple(
				(SymbolicTupleType) messageType.getDynamicType(universe),
				emptyMessageComponents);
		return message;
	}
}
