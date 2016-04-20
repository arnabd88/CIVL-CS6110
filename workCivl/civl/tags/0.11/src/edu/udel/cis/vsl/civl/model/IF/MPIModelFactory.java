package edu.udel.cis.vsl.civl.model.IF;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;

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
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public interface MPIModelFactory extends ModelFactory {

	static final String MPI_COMM_WORLD = "__MPI_Comm_world";
	
	static final String COMMM_CREATE = "$comm_create";
	
	/**
	 * The function name of MPI Send.
	 */
	static final String MPI_SEND = "MPI_Send";

	/**
	 * The function name of MPI Receive.
	 */
	static final String MPI_RECV = "MPI_Recv";

	/**
	 * The function name of MPI Barrier.
	 */
	static final String MPI_BARRIER = "MPI_Barrier";

	/**
	 * The function name of MPI Isend.
	 */
	static final String MPI_ISEND = "MPI_Isend";

	/**
	 * The function name of MPI Ireceive.
	 */
	static final String MPI_IRECV = "MPI_Irecv";

	/**
	 * The function name of MPI Wait.
	 */
	static final String MPI_WAIT = "MPI_Wait";

	MPISendStatement mpiSendStatement(CIVLSource source, Location location,
			LHSExpression lhs, ArrayList<Expression> arguments);

	/**
	 * Create a new location.
	 * 
	 * @param source
	 *            The CIVL source of the location
	 * @param scope
	 *            The scope containing this location.
	 * @return The new location.
	 */
	Location location(Scope scope);

	Variable variable(CIVLType type, Identifier name, int vid);

	Identifier identifier(String name);

	Scope scope(Scope parent, LinkedHashSet<Variable> variables,
			CIVLFunction function);

	/**
	 * An integer literal expression.
	 * 
	 * @param value
	 *            The (arbitrary precision) integer value.
	 * @return The integer literal expression.
	 */
	IntegerLiteralExpression integerLiteralExpression(BigInteger value);

	/**
	 * An assignment statement.
	 * 
	 * @param source
	 *            The source location for this statement.
	 * @param lhs
	 *            The left hand side of the assignment.
	 * @param rhs
	 *            The right hand side of the assignment.
	 * @param isInitialization
	 *            True iff the assign statement to create is translated from a
	 *            the initialization node of variable declaration node.
	 * @return A new assignment statement.
	 */
	AssignStatement assignStatement(Location source, LHSExpression lhs,
			Expression rhs, boolean isInitialization);

	/**
	 * A variable expression.
	 * 
	 * @param variable
	 *            The variable being referenced.
	 * @return The variable expression.
	 */
	VariableExpression variableExpression(Variable variable);

	/**
	 * A fork statement. Used to spawn a new process.
	 * 
	 * @param source
	 *            The source location for this fork statement.
	 * @param isCall
	 *            is this a call statement (not spawn statement)?
	 * @param function
	 *            A function
	 * @param arguments
	 *            The arguments to the function.
	 * @return A new fork statement.
	 */
	CallOrSpawnStatement callOrSpawnStatement(Location source, boolean isCall,
			CIVLFunction function, List<Expression> arguments);

	/**
	 * Create the rank variable.
	 * 
	 * @param scope
	 *            The scope that contains the rank variable. It should be the
	 *            top scope of the main function (i.e., the MPI process
	 *            function).
	 * 
	 * @param vid
	 *            The index of the variable in the scope. Usually vid ==
	 *            scope.NumOfVaraibles().
	 */
	void createRankVariable(int vid);

	/**
	 * Return the rank variable.
	 * 
	 * @return
	 */
	VariableExpression rankVariable();

	void createStartVariable(Scope scope, int vid);

	VariableExpression startVariable();

	void createProcsVariable(Scope scope, int vid, Expression nprocs);

	VariableExpression procsVariable();

	Expression numberOfProcs();

	void setNumberOfProcs(Expression numberExpression);

	MPIWaitStatement mpiWaitStatement(CIVLSource source, Location location,
			LHSExpression lhs, ArrayList<Expression> arguments);

	MPIBarrierStatement mpiBarrierStatement(CIVLSource source,
			Location location, LHSExpression lhs,
			ArrayList<Expression> arguments);

	MPIIrecvStatement mpiIrecvStatement(CIVLSource source, Location location,
			LHSExpression lhs, ArrayList<Expression> arguments);

	/**
	 * Translate a MPI_Irecv functionn call to an instance of
	 * {@link edu.udel.cis.vsl.civl.model.IF.statement.MPIIrecvStatement}
	 * 
	 * @param scope
	 *            The scope of this function call.
	 * @param functionCallNode
	 *            The AST node to be translated.
	 * @return A fragment containing exactly one statement, i.e., the MPI_Irecv
	 *         statement.
	 */
	MPIRecvStatement mpiRecvStatement(CIVLSource source, Location location,
			LHSExpression lhs, ArrayList<Expression> arguments);

	/**
	 * Create an instance of
	 * {@link edu.udel.cis.vsl.civl.model.IF.statement.MPIIsendStatement}.
	 * Called when translating an MPI_Isend function call.
	 * 
	 * @param source
	 *            The source code information of the MPI_Isend function call.
	 * @param location
	 *            The source location of the MPI_Isend statement
	 * @param scope
	 *            The scope of the MPI_Isend statement.
	 * @param lhs
	 *            The left hand side expression of the MPI_Isend function call.
	 * @param arguments
	 *            The list of arguments of the MPI_Isend statement.
	 * @return the new MPI_Isend statement.
	 */
	MPIIsendStatement mpiIsendStatement(CIVLSource source, Location location,
			LHSExpression lhs, ArrayList<Expression> arguments);

	CallOrSpawnStatement callOrSpawnStatement(Location source, boolean isCall,
			LHSExpression lhs, CIVLFunction function, List<Expression> arguments);
}
