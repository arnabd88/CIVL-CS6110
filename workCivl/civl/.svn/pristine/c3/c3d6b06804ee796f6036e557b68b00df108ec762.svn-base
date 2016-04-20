package edu.udel.cis.vsl.civl.model.common;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;

import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.MPIModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.IntegerLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.AssignStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.MPIBarrierStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.MPIIrecvStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.MPIIsendStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.MPIRecvStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.MPISendStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.MPIWaitStatement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.model.common.statement.CommonMPIBarrierStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonMPIIrecvStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonMPIIsendStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonMPIRecvStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonMPISendStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonMPIWaitStatement;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;

/**
 * This class translates MPI function call nodes into the corresponding MPI
 * Statements.
 * 
 * @author Ziqing Luo (ziqing)
 * @author Manchun Zheng (zmanchun)
 */
public class CommonMPIModelFactory extends CommonModelFactory implements
		MPIModelFactory {

	/* *************************** Static Fields *************************** */

	static final String RANK = "__rank";

	static final String MPI_START = "__mpi_start";

	static final String PROCS = "__procs";

	/* ************************** Instance Fields ************************** */

	/**
	 * The rank variable that stores the rank of each process. It is a parameter
	 * of the main function added by MPIFunctionTranslator.
	 */
	private VariableExpression rankVariable;

	/**
	 * A global variable in the root scope added by MPIFunctionTranslator. It
	 * synchronizes the starting of all MPI processes.
	 */
	private VariableExpression startVariable;

	/**
	 * A variable of array type in the root function's scope that stores the
	 * process id's of spawned MPI processes.
	 */
	private VariableExpression procsVariable;

	/**
	 * The expression that stores the value of the number of processes specified
	 * by users from the command line.
	 */
	private Expression numberOfProcs;

	/* **************************** Constructors *************************** */

	/**
	 * Create a new instance of MPIStatementFactory.
	 * 
	 * @param factory
	 *            The model factory to be used for translating AST nodes.
	 */
	public CommonMPIModelFactory(SymbolicUniverse universe) {
		super(universe);
	}

	/* ******************* Methods from MPIModelFactory ******************** */

	/**
	 * Translate a MPI_Send function call to an instance of
	 * {@link edu.udel.cis.vsl.civl.model.IF.statement.MPISendStatement}.
	 * 
	 * @param scope
	 *            The scope of this function call.
	 * @param functionCallNode
	 *            The AST node to be translated.
	 * @return A fragment containing exactly one statement, i.e., the MPI_Send
	 *         statement.
	 * 
	 */
	@Override
	public MPISendStatement mpiSendStatement(CIVLSource source,
			Location location, LHSExpression lhs,
			ArrayList<Expression> arguments) {
		CommonMPISendStatement sendStatement = new CommonMPISendStatement(
				source, location, lhs, arguments);
		Scope finalScope = null;

		if (lhs != null) {
			finalScope = join(lhs.expressionScope(), finalScope);
		}
		finalScope = join(finalScope, joinScope(arguments));
		sendStatement.setStatementScope(finalScope);
		return sendStatement;
	}

	/**
	 * Translate a MPI_Recv functionn call to an instance of
	 * {@link edu.udel.cis.vsl.civl.model.IF.statement.MPIRecvStatement}
	 * 
	 * @param scope
	 *            The scope of this function call.
	 * @param functionCallNode
	 *            The AST node to be translated.
	 * @return A fragment containing exactly one statement, i.e., the MPI_Recv
	 *         statement.
	 */
	@Override
	public MPIRecvStatement mpiRecvStatement(CIVLSource source,
			Location location, LHSExpression lhs,
			ArrayList<Expression> arguments) {
		CommonMPIRecvStatement recvStatement = new CommonMPIRecvStatement(
				source, location, lhs, arguments, this);
		Scope finalScope = null;

		if (lhs != null) {
			finalScope = join(lhs.expressionScope(), finalScope);
		}
		finalScope = join(finalScope, joinScope(arguments));
		recvStatement.setStatementScope(finalScope);
		return recvStatement;
	}

	@Override
	public MPIIsendStatement mpiIsendStatement(CIVLSource source,
			Location location, LHSExpression lhs,
			ArrayList<Expression> arguments) {
		CommonMPIIsendStatement isendStatement = new CommonMPIIsendStatement(
				source, location, lhs, arguments);
		Scope finalScope = null;

		if (lhs != null) {
			finalScope = join(lhs.expressionScope(), finalScope);
		}
		finalScope = join(finalScope, joinScope(arguments));
		isendStatement.setStatementScope(finalScope);
		return isendStatement;
	}

	@Override
	public MPIIrecvStatement mpiIrecvStatement(CIVLSource source,
			Location location, LHSExpression lhs,
			ArrayList<Expression> arguments) {
		CommonMPIIrecvStatement irecvStatement = new CommonMPIIrecvStatement(
				source, location, lhs, arguments);
		Scope finalScope = null;

		if (lhs != null) {
			finalScope = join(lhs.expressionScope(), finalScope);
		}
		finalScope = join(finalScope, joinScope(arguments));
		irecvStatement.setStatementScope(finalScope);
		return irecvStatement;
	}

	/**
	 * Translate a MPI_Wait functionn call to an instance of
	 * {@link edu.udel.cis.vsl.civl.model.IF.statement.MPIWaitStatement}
	 * 
	 * @param scope
	 *            The scope of this function call.
	 * @param functionCallNode
	 *            The AST node to be translated.
	 * @return A fragment containing exactly one statement, i.e., the MPI_Wait
	 *         statement.
	 */
	@Override
	public MPIWaitStatement mpiWaitStatement(CIVLSource source,
			Location location, LHSExpression lhs,
			ArrayList<Expression> arguments) {
		CommonMPIWaitStatement waitStatement = new CommonMPIWaitStatement(
				source, location, lhs, arguments);
		Scope finalScope = null;

		if (lhs != null) {
			finalScope = join(lhs.expressionScope(), finalScope);
		}
		finalScope = join(finalScope, joinScope(arguments));
		waitStatement.setStatementScope(finalScope);
		return waitStatement;
	}

	/**
	 * Translate a MPI_Barrier function call to an instance of
	 * {@link edu.udel.cis.vsl.civl.model.IF.statement.MPIBarrierStatement}
	 * 
	 * @param scope
	 *            The scope of this function call.
	 * @param functionCallNode
	 *            The AST node to be translated.
	 * @return A fragment containing exactly one statement, i.e., the
	 *         MPI_Barrier statement.
	 */
	@Override
	public MPIBarrierStatement mpiBarrierStatement(CIVLSource source,
			Location location, LHSExpression lhs,
			ArrayList<Expression> arguments) {
		// MPI_Barrier just have one argument--communicator
		CommonMPIBarrierStatement barrierStatement = new CommonMPIBarrierStatement(
				source, location, lhs, arguments.get(0));
		Scope finalScope = null;

		if (lhs != null) {
			finalScope = join(lhs.expressionScope(), finalScope);
		}
		finalScope = join(finalScope, joinScope(arguments));
		barrierStatement.setStatementScope(finalScope);
		return barrierStatement;
	}

	/* ******************** Methods from ModelFactory ********************** */

	@Override
	public Location location(Scope scope) {
		return location(systemSource(), scope);
	}

	@Override
	public Variable variable(CIVLType type, Identifier name, int vid) {
		return variable(systemSource(), type, name, vid);
	}

	@Override
	public Identifier identifier(String name) {
		return identifier(systemSource(), name);
	}

	@Override
	public Scope scope(Scope parent, LinkedHashSet<Variable> variables,
			CIVLFunction function) {
		return scope(systemSource(), parent, variables, function);
	}

	@Override
	public IntegerLiteralExpression integerLiteralExpression(BigInteger value) {
		return integerLiteralExpression(systemSource(), value);
	}

	@Override
	public AssignStatement assignStatement(Location source, LHSExpression lhs,
			Expression rhs, boolean isInitialization) {
		return assignStatement(systemSource(), source, lhs, rhs,
				isInitialization);
	}

	@Override
	public VariableExpression variableExpression(Variable variable) {
		return variableExpression(systemSource(), variable);
	}

	@Override
	public CallOrSpawnStatement callOrSpawnStatement(Location source,
			boolean isCall, CIVLFunction function, List<Expression> arguments) {
		return null;
	}

	@Override
	public CallOrSpawnStatement callOrSpawnStatement(Location source,
			boolean isCall, LHSExpression lhs, CIVLFunction function,
			List<Expression> arguments) {
		return null;
	}

	@Override
	public void createRankVariable(int vid) {
		Variable rankVariable = this.variable(this.integerType(),
				this.identifier(RANK), vid);
		this.rankVariable = this.variableExpression(rankVariable);
	}

	@Override
	public VariableExpression rankVariable() {
		return this.rankVariable;
	}

	@Override
	public void createStartVariable(Scope scope, int vid) {
		Variable startVariable = this.variable(this.integerType(),
				this.identifier(MPI_START), vid);
		this.startVariable = this.variableExpression(startVariable);
		scope.addVariable(startVariable);
	}

	@Override
	public VariableExpression startVariable() {
		return this.startVariable;
	}

	@Override
	public void createProcsVariable(Scope scope, int vid, Expression nprocs) {
		CIVLArrayType arrayType = completeArrayType(processType(), nprocs);
		Variable procsVariable = this.variable(arrayType,
				this.identifier(PROCS), vid);
		this.procsVariable = this.variableExpression(procsVariable);
		scope.addVariable(procsVariable);
	}

	@Override
	public VariableExpression procsVariable() {
		return this.procsVariable;
	}

	@Override
	public Expression numberOfProcs() {
		return this.numberOfProcs;
	}

	@Override
	public void setNumberOfProcs(Expression numberExpression) {
		this.numberOfProcs = numberExpression;
	}
}
