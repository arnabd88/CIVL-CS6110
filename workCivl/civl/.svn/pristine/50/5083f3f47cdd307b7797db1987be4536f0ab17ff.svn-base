package edu.udel.cis.vsl.civl.library.mpi;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import edu.udel.cis.vsl.abc.util.IF.Pair;
import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryExecutor;
import edu.udel.cis.vsl.civl.log.IF.CIVLExecutionException;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.Certainty;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPrimitiveType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.DynamicScope;
import edu.udel.cis.vsl.civl.state.IF.StackEntry;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * Implementation of system functions declared mpi.h.
 * <ul>
 * <li>
 * 
 * </li>
 * </ul>
 * 
 * @author ziqingluo
 * 
 */
public class LibmpiExecutor extends BaseLibraryExecutor implements
		LibraryExecutor {

	/**
	 * A map stores MPI process-status variables and the dynamic scopes in where
	 * they are. Key for the information is the process id of the process.
	 */
	private Map<Integer, Pair<Scope, Variable>> processStatusVariables;

	public LibmpiExecutor(String name, Executor primaryExecutor,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer, CIVLConfiguration civlConfig,
			LibraryExecutorLoader libExecutorLoader,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, primaryExecutor, modelFactory, symbolicUtil,
				symbolicAnalyzer, civlConfig, libExecutorLoader,
				libEvaluatorLoader);
		this.processStatusVariables = new HashMap<>();
	}

	@Override
	public State execute(State state, int pid, CallOrSpawnStatement statement,
			String functionName) throws UnsatisfiablePathConditionException {
		return this.executeWork(state, pid, statement, functionName);
	}

	/* ************************* private methods **************************** */

	private State executeWork(State state, int pid, Statement statement,
			String functionName) throws UnsatisfiablePathConditionException {
		Expression[] arguments;
		LHSExpression lhs;
		SymbolicExpression[] argumentValues;
		CallOrSpawnStatement call;
		int numArgs;
		String process = state.getProcessState(pid).name() + "(id=" + pid + ")";

		if (!(statement instanceof CallOrSpawnStatement)) {
			throw new CIVLInternalException("Unsupported statement for mpi",
					statement);
		}
		call = (CallOrSpawnStatement) statement;
		numArgs = call.arguments().size();
		arguments = new Expression[numArgs];
		argumentValues = new SymbolicExpression[numArgs];
		lhs = call.lhs();
		for (int i = 0; i < numArgs; i++) {
			Evaluation eval;

			arguments[i] = call.arguments().get(i);
			eval = evaluator.evaluate(state, pid, arguments[i]);
			argumentValues[i] = eval.value;
			state = eval.state;
		}
		switch (functionName) {
		case "MPI_Comm_size":
		case "MPI_Comm_rank":
		case "CMPI_Set_status":
			state = executeSetStatus(state, pid, call, arguments,
					argumentValues);
			break;
		case "CMPI_Get_status":
			state = executeGetStatus(state, pid, call);
			break;
		case "CMPI_AssertConsistentType":
			state = executeAssertConsistentType(state, pid, process, arguments,
					argumentValues, statement.getSource());
			break;
		case "CMPI_NewGcomm":
			state = executeNewGcomm(state, pid, process, lhs, arguments,
					argumentValues, statement.getSource());
			break;
		case "CMPI_GetGcomm":
			state = executeGetGcomm(state, pid, process, lhs, arguments,
					argumentValues, statement.getSource());
			break;
		case "CMPI_Root_scope":
			state = executeRootScope(state, pid, process, lhs, arguments,
					argumentValues, statement.getSource());
			break;
		case "CMPI_Proc_scope":
			state = executeProcScope(state, pid, process, lhs, arguments,
					argumentValues, statement.getSource());
			break;
		default:
			throw new CIVLInternalException("Unknown civlc function: " + name,
					statement);
		}
		state = stateFactory.setLocation(state, pid, call.target(),
				call.lhs() != null);
		return state;
	}

	/**
	 * Executes system function
	 * <code>CMPI_Set_status(__MPI_Sys_status__ newStatus)</code>. Set the
	 * variable "_my_status" added by
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
		Variable myStatusVar = null;
		// variable (right in pair) and it's dyscope
		Pair<Scope, Variable> myStatusVarInfo;
		State newState;
		int dyscopeId = -1;

		if (!this.processStatusVariables.keySet().contains(pid)) {
			// Set of children scopes of MPI_Process function
			Set<Scope> mpiProcChildren = model.function("MPI_Process")
					.outerScope().children();
			Scope procStaticScope;

			// It should exactly have a child which is the scope of the body
			assert mpiProcChildren.size() == 1;
			procStaticScope = mpiProcChildren.iterator().next();
			assert procStaticScope != null : "Failure of getting static scope of the body function of MPI process "
					+ pid + " .\n";
			myStatusVar = procStaticScope.variable("_my_status");
			assert myStatusVar != null : "Failure of getting variable '_my_status' in function 'MPI_Process()'";
			dyscopeId = this
					.getScopeInProcessStack(state, pid, procStaticScope);
			this.processStatusVariables.put(pid, new Pair<>(procStaticScope,
					myStatusVar));
		} else {
			myStatusVarInfo = this.processStatusVariables.get(pid);
			myStatusVar = myStatusVarInfo.right;
			dyscopeId = this.getScopeInProcessStack(state, pid,
					myStatusVarInfo.left);
		}
		newState = this.stateFactory.setVariable(state, myStatusVar.vid(),
				dyscopeId, newStatus);
		return newState;
	}

	private State executeGetStatus(State state, int pid,
			CallOrSpawnStatement call)
			throws UnsatisfiablePathConditionException {
		LHSExpression lhs = call.lhs();

		if (lhs != null) {
			// variable (right in pair) and it's static scope
			Pair<Scope, Variable> myStatusVarInfo;
			int dyscopeId = -1;
			Variable myStatusVar;
			SymbolicExpression valueOfMyStatusVar;
			String process = state.getProcessState(pid).name() + "(id=" + pid
					+ ")";

			if (!this.processStatusVariables.keySet().contains(pid)) {
				// Set of children scopes of MPI_Process function
				Set<Scope> mpiProcChildren = model.function("MPI_Process")
						.outerScope().children();
				Scope procStaticScope;

				// It should exactly have a child which is the scope of the body
				assert mpiProcChildren.size() == 1;
				procStaticScope = mpiProcChildren.iterator().next();
				assert procStaticScope != null : "Failure of getting static scope of the body function of MPI process "
						+ pid + " .\n";
				myStatusVar = procStaticScope.variable("_my_status");
				assert myStatusVar != null : "Failure of getting variable '_my_status' in function 'MPI_Process()'";
				dyscopeId = this.getScopeInProcessStack(state, pid,
						procStaticScope);
				this.processStatusVariables.put(pid, new Pair<>(
						procStaticScope, myStatusVar));
			} else {
				myStatusVarInfo = this.processStatusVariables.get(pid);
				myStatusVar = myStatusVarInfo.right;
				dyscopeId = this.getScopeInProcessStack(state, pid,
						myStatusVarInfo.left);
			}
			valueOfMyStatusVar = state.getDyscope(dyscopeId).getValue(
					myStatusVar.vid());
			return this.primaryExecutor.assign(state, pid, process, lhs,
					valueOfMyStatusVar);
		}
		return state;
	}

	/**
	 * TODO: I think this is a correct version of
	 * {@link State#getDyscope(int, Scope)} First searching the processState
	 * call stack, if the dynamic scope in the bottom of the stack is not
	 * corresponding to the given static scope, searching ancestors of that
	 * scope.
	 * 
	 * @param state
	 * @param pid
	 * @param targetScope
	 * @return
	 */
	private int getScopeInProcessStack(State state, int pid, Scope targetScope) {
		Iterator<? extends StackEntry> stackIter = state.getProcessState(pid)
				.getStackEntries().iterator();
		int staticSid = targetScope.id();
		DynamicScope currDyscope = null;
		int currStaticSid;

		while (stackIter.hasNext()) {
			int currDySid = stackIter.next().scope();

			currDyscope = state.getDyscope(currDySid);
			currStaticSid = currDyscope.lexicalScope().id();
			if (currStaticSid == staticSid)
				return currDySid;
		}
		// if the target scope is not in process call stack, search all parents
		// of the scope in the bottom of the call stack
		while (currDyscope.getParent() > 0) {
			int currDySid = currDyscope.getParent();

			currDyscope = state.getDyscope(currDySid);
			if (currDyscope.lexicalScope().id() == staticSid)
				return currDySid;
		}
		return -1;
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

		if (symbolicUtil.isNullPointer(pointer))
			return state;
		if (!pointer.operator().equals(SymbolicOperator.CONCRETE)
				|| !symbolicUtil.isValidPointer(pointer)) {
			errorLogger.reportError(new CIVLExecutionException(
					ErrorKind.POINTER, Certainty.CONCRETE, process,
					"Attempt to read/write a invalid pointer type variable",
					arguments[0].getSource()));
			return state;
		}
		reasoner = universe.reasoner(state.getPathCondition());
		realType = symbolicAnalyzer.getFlattenedArrayElementType(state,
				ptrSource, pointer);
		realSymType = realType.getDynamicType(universe);
		assertedTypeEnum = (IntegerNumber) reasoner.extractNumber(assertedType);
		assertedSymType = this.mpiTypeToCIVLType(assertedTypeEnum.intValue(),
				source).getDynamicType(universe);
		if (!assertedSymType.equals(realSymType)) {
			CIVLExecutionException err = new CIVLExecutionException(
					ErrorKind.MPI_ERROR,
					Certainty.CONCRETE,
					process,
					"The primitive type:"
							+ realType.toString()
							+ " of the object pointed by the input pointer argument of"
							+ " MPI routines is not consistent with the given MPI_Datatype",
					source);
			errorLogger.reportError(err);
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
				.variable("GCOMMS");
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
				.variable("GCOMMS");

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

		eval = evaluator.dereference(source, state, process, commHandle, false);
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
}
