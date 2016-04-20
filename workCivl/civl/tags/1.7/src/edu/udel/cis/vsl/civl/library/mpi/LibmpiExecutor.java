package edu.udel.cis.vsl.civl.library.mpi;

import java.util.Arrays;
import java.util.Iterator;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.comm.LibcommEvaluator;
import edu.udel.cis.vsl.civl.library.comm.LibcommExecutor;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryExecutor;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.contract.FunctionContract.ContractKind;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPrimitiveType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryLoaderException;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.semantics.contract.ContractEvaluator;
import edu.udel.cis.vsl.civl.state.IF.DynamicScope;
import edu.udel.cis.vsl.civl.state.IF.StackEntry;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.state.common.immutable.ImmutableCollectiveSnapshotsEntry;
import edu.udel.cis.vsl.civl.state.common.immutable.ImmutableState;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * Implementation of system functions declared mpi.h and civl-mpi.cvh
 * <ul>
 * <li>$mpi_set_status</li>
 * <li>$mpi_get_status</li>
 * <li>$mpi_assertConsistentType</li>
 * <li>$mpi_newGcomm</li>
 * <li>$mpi_getGcomm</li>
 * <li>$mpi_root_scope</li>
 * <li>$mpi_proc_scope</li>
 * <li>$mpi_isRecvBufEmpty</li>
 * </ul>
 * 
 * @author ziqingluo
 * 
 */
public class LibmpiExecutor extends BaseLibraryExecutor implements
		LibraryExecutor {

	public LibmpiExecutor(String name, Executor primaryExecutor,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer, CIVLConfiguration civlConfig,
			LibraryExecutorLoader libExecutorLoader,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, primaryExecutor, modelFactory, symbolicUtil,
				symbolicAnalyzer, civlConfig, libExecutorLoader,
				libEvaluatorLoader);
	}

	@Override
	public State execute(State state, int pid, CallOrSpawnStatement statement,
			String functionName) throws UnsatisfiablePathConditionException {
		return this.executeWork(state, pid, statement, functionName);
	}

	/**
	 * Execute MPI collective contract. MPI collective contract can be checked
	 * as collective assertions, but error will be reported as MPI Collective
	 * Contract violation.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param args
	 *            The expression array of arguments
	 * @param source
	 *            The source of the contract expression
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	public State executeCollectiveContract(State state, int pid,
			String process, Expression[] args, ContractKind kind,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression[] argumentValues = new SymbolicExpression[1];
		Evaluation eval;

		eval = evaluator.evaluate(state, pid, args[0]);
		state = eval.state;
		argumentValues[0] = eval.value;
		state = executeCoassertWorker(state, pid, process, args,
				argumentValues, source, true, kind);
		return state;
	}

	/* ************************* private methods **************************** */
	private State executeWork(State state, int pid,
			CallOrSpawnStatement statement, String functionName)
			throws UnsatisfiablePathConditionException {
		Expression[] arguments;
		LHSExpression lhs;
		SymbolicExpression[] argumentValues;
		CallOrSpawnStatement call;
		int numArgs;
		String process = state.getProcessState(pid).name() + "(id=" + pid + ")";

		call = statement;
		numArgs = call.arguments().size();
		arguments = new Expression[numArgs];
		for (int i = 0; i < numArgs; i++)
			arguments[i] = call.arguments().get(i);
		// If the function is $mpi_coassert, call function
		// "mpiCollectiveAssert()" which is a public re-usable function. It
		// deals with arguments of $mpi_coassert differently with other normal
		// system functions:
		if (functionName.equals("$mpi_coassert")) {
			state = executeCoassertArrive(state, pid, process, arguments,
					statement.getSource());
			return stateFactory.setLocation(state, pid, call.target(),
					call.lhs() != null);
		}
		argumentValues = new SymbolicExpression[numArgs];
		for (int i = 0; i < numArgs; i++) {
			Evaluation eval;

			eval = evaluator.evaluate(state, pid, arguments[i]);
			argumentValues[i] = eval.value;
			state = eval.state;
		}
		lhs = call.lhs();
		switch (functionName) {
		case "$mpi_set_status":
			state = executeSetStatus(state, pid, call, arguments,
					argumentValues);
			break;
		case "$mpi_get_status":
			state = executeGetStatus(state, pid, call);
			break;
		case "$mpi_assertConsistentType":
			state = executeAssertConsistentType(state, pid, process, arguments,
					argumentValues, statement.getSource());
			break;
		case "$mpi_newGcomm":
			state = executeNewGcomm(state, pid, process, lhs, arguments,
					argumentValues, statement.getSource());
			break;
		case "$mpi_getGcomm":
			state = executeGetGcomm(state, pid, process, lhs, arguments,
					argumentValues, statement.getSource());
			break;
		case "$mpi_root_scope":
			state = executeRootScope(state, pid, process, lhs, arguments,
					argumentValues, statement.getSource());
			break;
		case "$mpi_proc_scope":
			state = executeProcScope(state, pid, process, lhs, arguments,
					argumentValues, statement.getSource());
			break;
		case "$mpi_p2pSendShot":
			state = executeSendShot(state, pid, process, functionName,
					arguments, argumentValues, zero, statement.getSource());
			break;
		case "$mpi_colSendShot": {
			state = executeSendShot(state, pid, process, functionName,
					arguments, argumentValues, one, statement.getSource());
			break;
		}
		case "$mpi_p2pRecvShot":
			state = executeRecvShot(state, pid, process, functionName,
					arguments, argumentValues, zero, statement.getSource());
			break;
		case "$mpi_colRecvShot":
			state = executeRecvShot(state, pid, process, functionName,
					arguments, argumentValues, one, statement.getSource());
			break;
		default:
			throw new CIVLInternalException("Unknown civl-mpi function: "
					+ name, statement);
		}
		state = stateFactory.setLocation(state, pid, call.target(),
				call.lhs() != null);
		return state;
	}

	/**
	 * Executes system function
	 * <code>CMPI_Set_status($mpi_sys_status newStatus)</code>. Set the variable
	 * "_my_status" added by
	 * {@link edu.udel.cis.vsl.civl.transform.IF.MPI2CIVLTransformer} the given
	 * new value
	 * 
	 * @param state
	 *            the current state
	 * @param pid
	 *            the PID of the process
	 * @param call
	 *            the statement expression of the function call
	 * @param arguments
	 *            an array of expressions of arguments of the function
	 * @param argumentValues
	 *            an array of symbolic expressions of arguments of the function
	 * @return
	 */
	private State executeSetStatus(State state, int pid,
			CallOrSpawnStatement call, Expression[] arguments,
			SymbolicExpression[] argumentValues) {
		SymbolicExpression newStatus = argumentValues[0];
		Pair<Integer, Variable> myStatusVarInfo;
		State newState;

		myStatusVarInfo = getVariableWTDynamicScoping(state, pid,
				"_mpi_process", "_mpi_status");
		newState = this.stateFactory.setVariable(state,
				myStatusVarInfo.right.vid(), myStatusVarInfo.left, newStatus);
		return newState;
	}

	private State executeGetStatus(State state, int pid,
			CallOrSpawnStatement call)
			throws UnsatisfiablePathConditionException {
		LHSExpression lhs = call.lhs();

		if (lhs != null) {
			// variable (right in pair) and it's static scope
			Pair<Integer, Variable> myStatusVarInfo;
			SymbolicExpression valueOfMyStatusVar;
			String process = state.getProcessState(pid).name() + "(id=" + pid
					+ ")";

			myStatusVarInfo = getVariableWTDynamicScoping(state, pid,
					"_mpi_process", "_mpi_status");
			valueOfMyStatusVar = state.getDyscope(myStatusVarInfo.left)
					.getValue(myStatusVarInfo.right.vid());
			return this.primaryExecutor.assign(state, pid, process, lhs,
					valueOfMyStatusVar);
		}
		return state;
	}

	/**
	 * Search a variable with a scoping rule similar to dynamic scoping. Given a
	 * variable name and a function name, this method will search for each call
	 * stack entry e and all ancestors of e from the top stack entry e0, it
	 * looks for the first matched variable appears in the matched function
	 * scope.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param functionName
	 *            The name of the function
	 * @param varName
	 *            The name of the variable
	 * @return
	 */
	private Pair<Integer, Variable> getVariableWTDynamicScoping(State state,
			int pid, String functionName, String varName) {
		Iterator<? extends StackEntry> stackIter = state.getProcessState(pid)
				.getStackEntries().iterator();
		DynamicScope currDyscope = null;
		int currDyscopeId = -1;

		while (stackIter.hasNext()) {
			currDyscopeId = stackIter.next().scope();

			while (currDyscopeId > 0) {
				currDyscope = state.getDyscope(currDyscopeId);
				if (currDyscope.lexicalScope().containsVariable(varName))
					if (currDyscope.lexicalScope().function().name().name()
							.equals(functionName))
						return new Pair<>(currDyscopeId, currDyscope
								.lexicalScope().variable(varName));
				currDyscopeId = currDyscope.getParent();
			}
		}
		return new Pair<>(currDyscopeId, null);
	}

	/**
	 * Executing the function
	 * <code>CMPI_AssertConsistentType(void * ptr, int sizeofDatatype)</code>
	 * The function checks if the pointer points to a object whose size of data
	 * type is consistent with the given size of data type.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param arguments
	 *            {@link Expression}s of arguments of the system function
	 * @param argumentValues
	 *            {@link SymbolicExpression}s of arguments of the system
	 *            function
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeAssertConsistentType(State state, int pid,
			String process, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		CIVLSource ptrSource = arguments[0].getSource();
		SymbolicExpression pointer = argumentValues[0];
		NumericExpression assertedType = (NumericExpression) argumentValues[1];
		CIVLType realType;
		SymbolicType realSymType, assertedSymType;
		Reasoner reasoner;
		IntegerNumber assertedTypeEnum;
		Pair<BooleanExpression, ResultType> checkPointer;

		if (symbolicUtil.isNullPointer(pointer))
			return state;
		// this assertion doesn't need recovery:
		if (!pointer.operator().equals(SymbolicOperator.TUPLE)) {
			errorLogger
					.logSimpleError(arguments[0].getSource(), state, process,
							this.symbolicAnalyzer.stateInformation(state),
							ErrorKind.POINTER,
							"attempt to read/write a non-concrete pointer type variable");
			return state;
		}
		checkPointer = symbolicAnalyzer.isDerefablePointer(state, pointer);
		if (checkPointer.right != ResultType.YES) {
			errorLogger.logError(arguments[0].getSource(), state, process,
					this.symbolicAnalyzer.stateInformation(state),
					checkPointer.left, checkPointer.right, ErrorKind.POINTER,
					"attempt to read/write a invalid pointer type variable");
			return state;
		}
		reasoner = universe.reasoner(state.getPathCondition());
		realType = symbolicAnalyzer.getArrayBaseType(state, ptrSource, pointer);
		realSymType = realType.getDynamicType(universe);
		assertedTypeEnum = (IntegerNumber) reasoner.extractNumber(assertedType);
		assertedSymType = this.mpiTypeToCIVLType(assertedTypeEnum.intValue(),
				source).getDynamicType(universe);
		// assertion doesn't need recovery:
		if (!assertedSymType.equals(realSymType)) {
			errorLogger
					.logSimpleError(
							source,
							state,
							process,
							this.symbolicAnalyzer.stateInformation(state),
							ErrorKind.MPI_ERROR,
							"The primitive type "
									+ realType.toString()
									+ " of the object pointed by the input pointer argument ["
									+ ptrSource.getLocation()
									+ ":"
									+ arguments[0]
									+ "] of"
									+ " MPI routines is not consistent with the specified MPI_Datatype.");
		}
		return state;
	}

	/**
	 * add new CMPI_Gcomm to seq
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
	private State executeNewGcomm(State state, int pid, String process,
			LHSExpression lhs, Expression arguments[],
			SymbolicExpression argumentValues[], CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression mpiRootScope = argumentValues[0];
		SymbolicExpression newCMPIGcomm = argumentValues[1];
		int sid = modelFactory.getScopeId(arguments[0].getSource(),
				mpiRootScope);
		Variable gcommsVar = state.getDyscope(sid).lexicalScope()
				.variable("_mpi_gcomms");
		SymbolicExpression gcomms;
		NumericExpression idx;

		gcomms = state.getVariableValue(sid, gcommsVar.vid());
		idx = universe.length(gcomms);
		gcomms = universe.append(gcomms, newCMPIGcomm);
		state = stateFactory.setVariable(state, gcommsVar.vid(), sid, gcomms);
		if (lhs != null)
			state = this.primaryExecutor.assign(state, pid, process, lhs, idx);
		return state;
	}

	private State executeGetGcomm(State state, int pid, String process,
			LHSExpression lhs, Expression arguments[],
			SymbolicExpression argumentValues[], CIVLSource source)
			throws UnsatisfiablePathConditionException {
		NumericExpression index = (NumericExpression) argumentValues[1];
		SymbolicExpression scope = argumentValues[0];
		SymbolicExpression gcomms, gcomm;
		int sid = modelFactory.getScopeId(arguments[0].getSource(), scope);
		Variable gcommsVar = state.getDyscope(sid).lexicalScope()
				.variable("_mpi_gcomms");

		gcomms = state.getVariableValue(sid, gcommsVar.vid());
		gcomm = universe.arrayRead(gcomms, index);
		if (lhs != null)
			state = this.primaryExecutor
					.assign(state, pid, process, lhs, gcomm);
		return state;
	}

	private State executeRootScope(State state, int pid, String process,
			LHSExpression lhs, Expression arguments[],
			SymbolicExpression argumentValues[], CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression commHandle = argumentValues[0];
		SymbolicExpression gcommHandle;
		SymbolicExpression scopeVal;
		Evaluation eval;
		int sid;

		eval = evaluator.dereference(source, state, process, arguments[0],
				commHandle, false);
		state = eval.state;
		gcommHandle = universe.tupleRead(eval.value, oneObject);
		sid = symbolicUtil.getDyscopeId(source, gcommHandle);
		scopeVal = modelFactory.scopeValue(sid);
		if (lhs != null)
			return this.primaryExecutor.assign(state, pid, process, lhs,
					scopeVal);
		return state;
	}

	private State executeProcScope(State state, int pid, String process,
			LHSExpression lhs, Expression arguments[],
			SymbolicExpression argumentValues[], CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression commHandle = argumentValues[0];
		SymbolicExpression scopeVal;
		int sid;

		sid = symbolicUtil.getDyscopeId(source, commHandle);
		scopeVal = modelFactory.scopeValue(sid);
		if (lhs != null)
			return this.primaryExecutor.assign(state, pid, process, lhs,
					scopeVal);
		return state;
	}

	/**
	 * Execute $mpi_coassert(MPI_Comm, _Bool). The second argument shall not be
	 * evaluated at calling phase. It will be evaluated at some point following
	 * collective assertion semantics. See
	 * {@link #executeCoassertWorker(State, int, String, Expression[], SymbolicExpression[], CIVLSource, boolean)}
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param arguments
	 *            The Expression array of the arguments
	 * @param source
	 *            The CIVLSource of the function call statement
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeCoassertArrive(State state, int pid, String process,
			Expression[] arguments, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression[] argumentValues = new SymbolicExpression[1];
		Evaluation eval;

		eval = evaluator.evaluate(state, pid, arguments[0]);
		state = eval.state;
		argumentValues[0] = eval.value;
		state = executeCoassertWorker(state, pid, process, arguments,
				argumentValues, source, false, null);
		return state;
	}

	/**
	 * Executing $mpi_coassert(MPI_Comm, _Bool) function with a regular snapshot
	 * semantics. The first process will create a collective entry and takes a
	 * snapshot on itself; others just save their snapshots; the last one who
	 * completes the entry will dequeue the entry an evaluates the snapshots all
	 * together.
	 * 
	 * @param call
	 *            the function call statement
	 * @param state
	 *            the current state
	 * @param pid
	 *            the Process ID
	 * @param process
	 *            the String Identifier of the process
	 * @param arguments
	 *            The expression array of the arguments of the function
	 * @param argumentValues
	 *            The symbolic expression array of the argument of the function
	 * @param source
	 * @param isContract
	 *            flag controls whether an error will be reported as a contract
	 *            violation or assertion violation
	 * @param kind
	 *            {@link ContractClauseKind} if the the collective entry is
	 *            associated to a contract, if it is associated to a collective
	 *            assert, kind is null.
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeCoassertWorker(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source, boolean isContract, ContractKind kind)
			throws UnsatisfiablePathConditionException {
		ImmutableState tmpState = (ImmutableState) state;
		Expression MPICommExpr = arguments[0];
		Expression assertion = arguments[1];
		// Symbolic Expressions
		SymbolicExpression MPIComm = argumentValues[0];
		SymbolicExpression colCommHandle = universe.tupleRead(MPIComm,
				universe.intObject(LibmpiEvaluator.colCommField));
		NumericExpression symNprocs;
		NumericExpression symPlace;
		NumericExpression symQueueID = (NumericExpression) universe.tupleRead(
				MPIComm, universe.intObject(4));
		SymbolicExpression colGcomm, colGcommHandle, colComm;
		ImmutableCollectiveSnapshotsEntry[] queue;
		boolean createNewEntry;
		boolean entryComplete;
		IntegerNumber tmpNumber;
		int place, nprocs;
		int queueLength;
		int queueID;
		Evaluation eval;

		eval = evaluator.dereference(MPICommExpr.getSource(), tmpState,
				process, MPICommExpr, colCommHandle, false);
		tmpState = (ImmutableState) eval.state;
		colComm = eval.value;
		colGcommHandle = universe.tupleRead(colComm, oneObject);
		eval = evaluator.dereference(MPICommExpr.getSource(), tmpState,
				process, MPICommExpr, colGcommHandle, false);
		tmpState = (ImmutableState) eval.state;
		colGcomm = eval.value;
		// reads and makes following variables concrete:
		// place: another name for ranks of process in MPI communicator
		// nprocs: number of processes
		symPlace = (NumericExpression) universe.tupleRead(colComm, zeroObject);
		symNprocs = (NumericExpression) universe
				.tupleRead(colGcomm, zeroObject);
		tmpNumber = (IntegerNumber) universe.extractNumber(symPlace);
		assert tmpNumber != null : "The place of a process in MPI should be concrete.";
		place = tmpNumber.intValue();
		tmpNumber = (IntegerNumber) universe.extractNumber(symNprocs);
		assert tmpNumber != null : "The number of processes in MPI should be concrete.";
		nprocs = tmpNumber.intValue();
		tmpNumber = (IntegerNumber) universe.extractNumber(symQueueID);
		assert tmpNumber != null : "The index of CMPI_Gcomm should be concrete.";
		queueID = tmpNumber.intValue();
		// CASE ONE: find out the entry this process should mark, if no such
		// entry,
		// create one.
		createNewEntry = true; // if no corresponding entry there
		entryComplete = false; // if the entry is completed
		queue = stateFactory.getSnapshotsQueue(tmpState, queueID);
		if (queue != null) {
			queueLength = queue.length;
			for (int entryPos = 0; entryPos < queueLength; entryPos++) {
				ImmutableCollectiveSnapshotsEntry entry = queue[entryPos];

				if (!entry.isRecorded(place)) {
					createNewEntry = false;
					tmpState = stateFactory.addToCollectiveSnapshotsEntry(
							tmpState, pid, place, queueID, entryPos, assertion);
					entryComplete = stateFactory.getSnapshotsQueue(tmpState,
							queueID)[0].isComplete();
					break;
				}
			}
		}
		// CASE TWO: if it needs a new entry, then create it
		if (createNewEntry) {
			SymbolicExpression channels = null;

			if (civlConfig.isEnableMpiContract()) {
				SymbolicExpression colChannel = universe
						.tupleRead(colGcomm, universe
								.intObject(LibcommEvaluator.messageBufferField));
				SymbolicExpression p2pChannel = this.getchannelsFromCommHandle(
						tmpState, pid, process, MPICommExpr,
						universe.tupleRead(MPIComm, universe
								.intObject(LibmpiEvaluator.p2pCommField)));

				channels = universe.array(colChannel.type(),
						Arrays.asList(p2pChannel, colChannel));
			}
			// change the corresponding CollectiveSnapshotsEntry
			tmpState = stateFactory.createCollectiveSnapshotsEnrty(tmpState,
					pid, nprocs, place, queueID, assertion, channels, kind);
			entryComplete = (1 == nprocs);
		}
		// CASE THREE: if the entry is completed ?
		if (entryComplete)
			return dequeueCollectiveEntryAndEvaluation(tmpState, queueID,
					MPICommExpr, isContract);
		return tmpState;
	}

	private CIVLPrimitiveType mpiTypeToCIVLType(int MPI_TYPE, CIVLSource source) {
		switch (MPI_TYPE) {
		case 0: // char
			return typeFactory.charType();
		case 1: // character
			return typeFactory.charType();
		case 8: // int
			return typeFactory.integerType();
		case 20: // long
			return typeFactory.integerType();
		case 22: // float
			return typeFactory.realType();
		case 23: // double
			return typeFactory.realType();
		case 24: // long double
			return typeFactory.realType();
		case 27: // long long
			return typeFactory.integerType();
		case 39: // 2int
			return typeFactory.integerType();
		default:
			throw new CIVLUnimplementedFeatureException(
					"CIVL doesn't have such a CIVLPrimitiveType", source);
		}
		/*
		 * MPI_CHAR, MPI_CHARACTER, MPI_SIGNED_CHAR, MPI_UNSIGNED_CHAR,
		 * MPI_BYTE, MPI_WCHAR, MPI_SHORT, MPI_UNSIGNED_SHORT, MPI_INT,
		 * MPI_INT16_T, MPI_INT32_T, MPI_INT64_T, MPI_INT8_T, MPI_INTEGER,
		 * MPI_INTEGER1, MPI_INTEGER16, MPI_INTEGER2, MPI_INTEGER4,
		 * MPI_INTEGER8, MPI_UNSIGNED, MPI_LONG, MPI_UNSIGNED_LONG, MPI_FLOAT,
		 * MPI_DOUBLE, MPI_LONG_DOUBLE, MPI_LONG_LONG_INT,
		 * MPI_UNSIGNED_LONG_LONG, MPI_LONG_LONG, MPI_PACKED, MPI_LB, MPI_UB,
		 * MPI_UINT16_T, MPI_UINT32_T, MPI_UINT64_T, MPI_UINT8_T, MPI_FLOAT_INT,
		 * MPI_DOUBLE_INT, MPI_LONG_INT, MPI_SHORT_INT, MPI_2INT,
		 * MPI_LONG_DOUBLE_INT, MPI_AINT, MPI_OFFSET, MPI_2DOUBLE_PRECISION,
		 * MPI_2INTEGER, MPI_2REAL, MPI_C_BOOL, MPI_C_COMPLEX,
		 * MPI_C_DOUBLE_COMPLEX, MPI_C_FLOAT_COMPLEX, MPI_C_LONG_DOUBLE_COMPLEX,
		 * MPI_COMPLEX, MPI_COMPLEX16, MPI_COMPLEX32, MPI_COMPLEX4,
		 * MPI_COMPLEX8, MPI_REAL, MPI_REAL16, MPI_REAL2, MPI_REAL4, MPI_REAL8
		 */
	}

	/**
	 * Dequeues a complete collective entry and evaluates assertions of it.
	 * 
	 * @param state
	 *            The state that the collective entry just completes
	 * @param queueID
	 *            The ID associates to an MPI communicator, which is also used
	 *            to identify a collective queue.
	 * @param MPICommExpr
	 *            The expression of an MPI communicator
	 * @param isContrac
	 *            Flag indicates whether the evaluation is for a collective
	 *            contract or assert.
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State dequeueCollectiveEntryAndEvaluation(State state, int queueID,
			Expression MPICommExpr, boolean isContract)
			throws UnsatisfiablePathConditionException {
		ImmutableCollectiveSnapshotsEntry entry;
		ImmutableState mergedState;

		entry = stateFactory.peekCollectiveSnapshotsEntry(state, queueID);
		mergedState = stateFactory.mergeMonostates(state, entry);
		collectiveEvaluation(mergedState, entry.getAllAssertions(),
				MPICommExpr, isContract);
		state = stateFactory.dequeueCollectiveSnapshotsEntry(state, queueID);
		return state;
	}

	/**
	 * Evaluating assertions for all processes participating a $mpi_coassert()
	 * (or a collective contract) function.
	 * 
	 * @param mergedState
	 *            The state on where the evaluation happens
	 * @param assertions
	 *            The list of assertions, one for each process
	 * @param pid
	 *            The PID of the process
	 * @param group
	 *            The expression of the group contains all participated
	 *            processes
	 * @param isContract
	 *            Flag indicate whether those assertions are coming from a
	 *            collective assert or a collective contract
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State collectiveEvaluation(State mergedState,
			Expression[] assertions, Expression group, boolean isContract)
			throws UnsatisfiablePathConditionException {
		String process;
		Evaluation eval;
		Reasoner reasoner;
		Evaluator coEvaluator;

		coEvaluator = (isContract) ? new ContractEvaluator(modelFactory,
				stateFactory, libEvaluatorLoader, symbolicUtil,
				symbolicAnalyzer, null, errorLogger, civlConfig) : evaluator;
		stateFactory.simplify(mergedState);
		for (int place = 0; place < assertions.length; place++) {
			Expression snapShotAssertion = assertions[place];
			BooleanExpression assertionVal;
			ResultType resultType;
			String message;

			eval = coEvaluator.evaluate(mergedState, place, snapShotAssertion);
			mergedState = eval.state;
			assertionVal = (BooleanExpression) eval.value;
			reasoner = universe.reasoner(mergedState.getPathCondition());
			resultType = reasoner.valid(assertionVal).getResultType();
			if (!resultType.equals(ResultType.YES)) {
				Expression[] args = { snapShotAssertion };
				SymbolicExpression[] argVals = { assertionVal };

				// Contracts don't need recovery:
				if (isContract) {
					mergedState = this.primaryExecutor.reportContractViolation(
							mergedState, snapShotAssertion.getSource(), place,
							resultType, assertionVal, snapShotAssertion,
							ErrorKind.MPI_ERROR, group.toString());
				} else {
					message = " assertion:" + assertions[place];
					process = "process with rank: " + place
							+ " participating the " + "$mpi_coassert().";
					mergedState = this.reportAssertionFailure(mergedState,
							place, process, resultType,
							"$mpi_coassert violation: " + message, args,
							argVals, snapShotAssertion.getSource(),
							assertionVal, 1);
				}
			}
		}
		return mergedState;
	}

	private SymbolicExpression getchannelsFromCommHandle(State state, int pid,
			String process, Expression expr, SymbolicExpression commHandle)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluator.dereference(expr.getSource(), state,
				process, expr, commHandle, false);
		SymbolicExpression comm, gcomm, gcommHandle;

		comm = eval.value;
		gcommHandle = universe.tupleRead(comm,
				universe.intObject(LibcommEvaluator.gcommHandleInCommField));
		eval = evaluator.dereference(expr.getSource(), eval.state, process,
				expr, gcommHandle, false);
		gcomm = eval.value;
		return universe.tupleRead(gcomm,
				universe.intObject(LibcommEvaluator.messageBufferField));
	}

	/**
	 * * Executes the system functions
	 * <code>$system void $mpi_p2pSendShot(int commID, int source, int dest, int tag);</code>
	 * and
	 * <code>$system void $mpi_colSendShot(int commID, int source, int dest, int tag);</code>
	 * 
	 * <p>
	 * This method finds out the corresponding snapshots queue then do a message
	 * send on all unrecorded snapshot entries in that queue. Here an unrecorded
	 * snapshot entry is the entry that hasn't been reached by this process.
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param function
	 *            The function name of the executed function, used for error
	 *            reporting
	 * @param arguments
	 *            Expression arrays of arguments.
	 * @param argumentValues
	 *            SymbolicExpression arrays of arguments
	 * @param channelIdx
	 *            The channel index. It shall be either zero or one which
	 *            denotes weather the modification happens on point-2-point
	 *            buffer or collective buffer
	 * @param civlsource
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeSendShot(State state, int pid, String process,
			String function, Expression[] arguments,
			SymbolicExpression[] argumentValues, NumericExpression channelIdx,
			CIVLSource civlsource) throws UnsatisfiablePathConditionException {
		ImmutableState tmpState = (ImmutableState) state;
		ImmutableCollectiveSnapshotsEntry[] queue;
		SymbolicExpression[] msgBuffers;
		int mpiCommIdInt, queueLength;

		// MPI_Comm ID should always be concrete:
		mpiCommIdInt = ((IntegerNumber) universe
				.extractNumber((NumericExpression) argumentValues[0]))
				.intValue();
		queue = stateFactory.getSnapshotsQueue(tmpState, mpiCommIdInt);
		if (queue != null && queue.length > 0) {
			// change entries in the queue
			queueLength = queue.length;
			msgBuffers = new SymbolicExpression[queueLength];
			for (int i = 0; i < queueLength; i++) {
				ImmutableCollectiveSnapshotsEntry entry = queue[i];
				SymbolicExpression twoBuffers;
				int place = ((IntegerNumber) universe
						.extractNumber((NumericExpression) argumentValues[2]))
						.intValue();

				twoBuffers = entry.getMsgBuffers();
				if (!entry.isRecorded(place)) {
					if (twoBuffers != null) {
						SymbolicExpression channel;

						channel = universe.arrayRead(twoBuffers, channelIdx);
						channel = doMPISendOnSnapshots(state, process,
								function, channel, argumentValues[1],
								civlsource);
						twoBuffers = universe.arrayWrite(twoBuffers,
								channelIdx, channel);
					}
				}
				msgBuffers[i] = twoBuffers;
			}
			state = stateFactory.commitUpdatedChannelsToEntries(tmpState,
					mpiCommIdInt, msgBuffers);
		}
		return state;
	}

	/**
	 * Executes the system functions
	 * <code>$system void $mpi_p2pRecvShot(int commID, int source, int dest, int tag);</code>
	 * and
	 * <code>$system void $mpi_colRecvShot(int commID, int source, int dest, int tag);</code>
	 * 
	 * <p>
	 * This method finds out the corresponding snapshots queue then do a message
	 * receive on all unrecorded snapshot entries in that queue. Here an
	 * unrecorded snapshot entry is the entry that hasn't been reached by this
	 * process.
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param function
	 *            The function name of the executed function, used for error
	 *            reporting
	 * @param arguments
	 *            Expression arrays of arguments.
	 * @param argumentValues
	 *            SymbolicExpression arrays of arguments
	 * @param channelIdx
	 *            The channel index. It shall be either zero or one which
	 *            denotes weather the modification happens on point-2-point
	 *            buffer or collective buffer
	 * @param civlsource
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeRecvShot(State state, int pid, String process,
			String function, Expression[] arguments,
			SymbolicExpression[] argumentValues, NumericExpression channelIdx,
			CIVLSource civlsource) throws UnsatisfiablePathConditionException {
		ImmutableState tmpState = (ImmutableState) state;
		ImmutableCollectiveSnapshotsEntry[] queue;
		int mpiCommIdInt, queueLength;
		SymbolicExpression[] msgBuffers;
		NumericExpression src, dest, tag;
		// Flag: is there any entry in queue being modified.
		boolean anyEntryModified = false;
		int place;

		src = (NumericExpression) argumentValues[1];
		dest = (NumericExpression) argumentValues[2];
		tag = (NumericExpression) argumentValues[3];
		// MPI_Comm ID should always be concrete:
		mpiCommIdInt = ((IntegerNumber) universe
				.extractNumber((NumericExpression) argumentValues[0]))
				.intValue();
		queue = stateFactory.getSnapshotsQueue(tmpState, mpiCommIdInt);
		place = ((IntegerNumber) universe
				.extractNumber((NumericExpression) argumentValues[2]))
				.intValue();
		if (queue != null && queue.length > 0) {
			// change entries in the queue
			queueLength = queue.length;
			msgBuffers = new SymbolicExpression[queueLength];
			for (int i = 0; i < queueLength; i++) {
				SymbolicExpression twoMsgBuffers;
				ImmutableCollectiveSnapshotsEntry entry = queue[i];

				if (!entry.isRecorded(place)) {
					twoMsgBuffers = entry.getMsgBuffers();
					anyEntryModified = true;
					if (twoMsgBuffers != null) {
						SymbolicExpression msgBuffer = universe.arrayRead(
								twoMsgBuffers, channelIdx);

						msgBuffer = doMPIRecvOnSnapshots(tmpState, pid,
								process, function, msgBuffer, src, dest, tag,
								civlsource);
						twoMsgBuffers = universe.arrayWrite(twoMsgBuffers,
								channelIdx, msgBuffer);
						msgBuffers[i] = twoMsgBuffers;
					} else
						msgBuffers[i] = null;
				} else
					msgBuffers[i] = entry.getMsgBuffers();
			}
			if (anyEntryModified)
				state = stateFactory.commitUpdatedChannelsToEntries(tmpState,
						mpiCommIdInt, msgBuffers);
		}
		return state;
	}

	/**
	 * Loads the "comm" library executor to do a message enqueue operation on
	 * the given message channel.
	 * 
	 * @param state
	 *            The current state
	 * @param process
	 *            The String identifier of the process
	 * @param function
	 *            The name of the function
	 * @param channel
	 *            The Symbolic Expression of the message channel
	 * @param msg
	 *            The Symbolic Expression of the message
	 * @param civlsource
	 *            The {@link CIVLSource} of where in the source file causes this
	 *            execution
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private SymbolicExpression doMPISendOnSnapshots(State state,
			String process, String function, SymbolicExpression channel,
			SymbolicExpression msg, CIVLSource civlsource)
			throws UnsatisfiablePathConditionException {
		LibcommExecutor libexecutor;

		try {
			libexecutor = (LibcommExecutor) libExecutorLoader
					.getLibraryExecutor("comm", primaryExecutor, modelFactory,
							symbolicUtil, symbolicAnalyzer);
			return libexecutor.putMsgInChannel(channel, msg, civlsource);
		} catch (LibraryLoaderException e) {
			StringBuffer message = new StringBuffer();

			message.append("unable to load the library executor for the library"
					+ " comm for the function " + function);
			errorLogger.logSimpleError(civlsource, state, process,
					this.symbolicAnalyzer.stateInformation(state),
					ErrorKind.LIBRARY, message.toString());
			throw new UnsatisfiablePathConditionException();
		}
	}

	/**
	 * Loads the "comm" library executor to do a message dequeue operation on
	 * the given message channel.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param function
	 *            The name of the function
	 * @param channel
	 *            The Symbolic Expression of the message channel
	 * @param src
	 *            The Symbolic Expression of the source of the message
	 * @param dest
	 *            The Symbolic Expression of the destination of the message
	 * @param tag
	 *            The Symbolic Expression of the message tag
	 * @param civlsource
	 *            The {@link CIVLSource} of where the source file causes this
	 *            execution.
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private SymbolicExpression doMPIRecvOnSnapshots(State state, int pid,
			String process, String function, SymbolicExpression channel,
			NumericExpression src, NumericExpression dest,
			NumericExpression tag, CIVLSource civlsource)
			throws UnsatisfiablePathConditionException {
		LibcommExecutor libexecutor;

		try {
			libexecutor = (LibcommExecutor) libExecutorLoader
					.getLibraryExecutor("comm", primaryExecutor, modelFactory,
							symbolicUtil, symbolicAnalyzer);
			return libexecutor.getMsgOutofChannel(state, pid, process, channel,
					src, dest, tag, civlsource).right;
		} catch (LibraryLoaderException e) {
			StringBuffer message = new StringBuffer();

			message.append("unable to load the library executor for the library comm"
					+ " for the function " + function);
			errorLogger.logSimpleError(civlsource, state, process,
					this.symbolicAnalyzer.stateInformation(state),
					ErrorKind.LIBRARY, message.toString());
			throw new UnsatisfiablePathConditionException();
		}
	}
}
