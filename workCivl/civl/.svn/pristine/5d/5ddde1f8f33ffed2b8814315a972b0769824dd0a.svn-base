package edu.udel.cis.vsl.civl.library.mpi;

import java.io.PrintStream;
import java.util.HashSet;
import java.util.Set;

import edu.udel.cis.vsl.civl.err.CIVLInternalException;
import edu.udel.cis.vsl.civl.err.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.MPIModelFactory;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.AddressOfExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.semantics.Evaluation;
import edu.udel.cis.vsl.civl.semantics.Evaluator;
import edu.udel.cis.vsl.civl.semantics.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
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
public class Libmpi implements LibraryExecutor {

	private Executor primaryExecutor;

	private Evaluator evaluator;

	private SymbolicUniverse universe;

	private MPIModelFactory mpiFactory;
	
	private StateFactory stateFactory;

//	private NumericExpression zero;
//
//	private NumericExpression one;
//
//	private IntObject zeroObject;
//
//	private IntObject oneObject;

	public Libmpi(Executor primaryExecutor, PrintStream output,
			boolean enablePrintf, ModelFactory modelFactory) {
		this.primaryExecutor = primaryExecutor;
		this.evaluator = primaryExecutor.evaluator();
		// this.log = evaluator.log();
		this.universe = evaluator.universe();
		this.stateFactory = evaluator.stateFactory();
		this.mpiFactory = (MPIModelFactory)modelFactory;
		// this.zero = universe.zeroInt();
		// this.one = universe.oneInt();
		// this.zeroObject = universe.intObject(0);
		// this.oneObject = universe.intObject(1);
	}

	@Override
	public String name() {
		return "mpi";
	}

	@Override
	public State execute(State state, int pid, Statement statement)
			throws UnsatisfiablePathConditionException {
		return this.executeWork(state, pid, statement);
	}

	@Override
	public BooleanExpression getGuard(State state, int pid, Statement statement) {
		BooleanExpression guard;
		guard = universe.trueExpression();
		return guard;
	}

	@Override
	public boolean containsFunction(String name) {
		Set<String> functions = new HashSet<String>();
		functions.add("MPI_Comm_size");
		functions.add("MPI_Comm_rank");
		return functions.contains(name);
	}

	@Override
	public State initialize(State state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public State wrapUp(State state) {
		// TODO Auto-generated method stub
		return null;
	}

	/* ************************* private methods **************************** */
	/**
	 * Executing MPI_Comm_size routine, assigning the number of processes in a
	 * specific communicator to the second parameter.
	 * 
	 * TODO: implement the routine for specific comm instead of MPI_COMM_WORLD
	 * 
	 * @param state
	 * @param pid
	 * @param lhs
	 * @param arguments
	 * @param argumentValues
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeMPI_Comm_size(State state, int pid, LHSExpression lhs,
			Expression[] arguments, SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluator.evaluate(state, pid, this.mpiFactory.numberOfProcs());
		state = eval.state;
		SymbolicExpression nprocsValue = eval.value;
		AddressOfExpression nprocs = (AddressOfExpression)arguments[1];

		if (lhs != null) {
			eval = evaluator.evaluate(state, pid, lhs);
			state = eval.state;
			SymbolicExpression lhsValue = eval.value;
			state = this.primaryExecutor.assign(state, pid, lhs, lhsValue);
		}
		state = this.primaryExecutor.assign(state, pid, nprocs.operand(),
				nprocsValue);
		return state;
	}

	/**
	 * Executing MPI_Comm_rank routine, assigning the rank of the process in a
	 * specific communicator to the second parameter.
	 * 
	 * TODO: implement the routine for specific comm instead of MPI_COMM_WORLD
	 * 
	 * @param state
	 * @param pid
	 * @param lhs
	 * @param arguments
	 * @param argumentValues
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeMPI_Comm_rank(State state, int pid, LHSExpression lhs,
			Expression[] arguments, SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluator.evaluate(state, pid, this.mpiFactory.rankVariable());
		state = eval.state;
		SymbolicExpression rankValue = eval.value;
		AddressOfExpression rank = (AddressOfExpression)arguments[1];

		if (lhs != null) {
			eval = evaluator.evaluate(state, pid, lhs);
			state = eval.state;
			SymbolicExpression lhsValue = eval.value; 
			state = this.primaryExecutor.assign(state, pid, lhs, lhsValue);
		}
		state = this.primaryExecutor.assign(state, pid, rank.operand(),
				rankValue);
		
		return state;
	}
	
//	private State executeMPI_Init(State state, int pid, LHSExpression lhs,
//			Expression[] arguments, SymbolicExpression[] argumentValues)
//			throws UnsatisfiablePathConditionException {
//		Evaluation eval = evaluator.evaluate(state, pid, this.mpiFactory.numberOfProcs());
//		state = eval.state;
//		SymbolicExpression nprocs = eval.value;
//		SymbolicExpression comm = null;
//		SymbolicExpression messageBuffer = null;
//		SymbolicExpression messageBuferRow = null;
//		NumericExpression size = null;
//		Model model = state.getScope(0).lexicalScope().model();
//		CIVLType queueType = model.queueType();
//		CIVLType messageType = model.mesageType();
//		CIVLType commType = model.commType();
//		SymbolicType dynamicQueueType = queueType.getDynamicType(universe);
//		SymbolicType dynamicMessageType = messageType.getDynamicType(universe);
//		SymbolicExpression emptyQueue;
//		
//		
//		
//		return state;
//	}

	private State executeWork(State state, int pid, Statement statement)
			throws UnsatisfiablePathConditionException {
		Identifier name;
		Expression[] arguments;
		SymbolicExpression[] argumentValues;
		CallOrSpawnStatement call;
		LHSExpression lhs;
		int numArgs;

		if (!(statement instanceof CallOrSpawnStatement)) {
			throw new CIVLInternalException("Unsupported statement for mpi",
					statement);
		}
		call = (CallOrSpawnStatement) statement;
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
		case "MPI_Comm_size":
			state = this.executeMPI_Comm_size(state, pid, lhs, arguments,
					argumentValues);
			break;
		case "MPI_Comm_rank":
			state = this.executeMPI_Comm_rank(state, pid, lhs, arguments,
					argumentValues);
			break;
		default:
			throw new CIVLInternalException("Unknown civlc function: " + name,
					statement);
		}
		state = stateFactory.setLocation(state, pid, statement.target());
		return state;
	}
}
