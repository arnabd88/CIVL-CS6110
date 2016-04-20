package edu.udel.cis.vsl.civl.library.mpi;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import edu.udel.cis.vsl.abc.util.IF.Pair;
import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryExecutor;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
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
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

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
	public State execute(State state, int pid, CallOrSpawnStatement statement)
			throws UnsatisfiablePathConditionException {
		return this.executeWork(state, pid, statement);
	}

	/* ************************* private methods **************************** */

	private State executeWork(State state, int pid, Statement statement)
			throws UnsatisfiablePathConditionException {
		Identifier name;
		Expression[] arguments;
		SymbolicExpression[] argumentValues;
		CallOrSpawnStatement call;
		int numArgs;

		if (!(statement instanceof CallOrSpawnStatement)) {
			throw new CIVLInternalException("Unsupported statement for mpi",
					statement);
		}
		call = (CallOrSpawnStatement) statement;
		numArgs = call.arguments().size();
		name = call.function().name();
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
		case "MPI_Comm_size":
		case "MPI_Comm_rank":
		case "CMPI_Set_status":
			state = executeSetStatus(state, pid, call, arguments,
					argumentValues);
			break;
		case "CMPI_Get_status":
			state = executeGetStatus(state, pid, call);
			break;
		default:
			throw new CIVLInternalException("Unknown civlc function: " + name,
					statement);
		}
		state = stateFactory.setLocation(state, pid, call.target());
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
}
