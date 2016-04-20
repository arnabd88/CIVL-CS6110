package edu.udel.cis.vsl.civl.transform.common;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode.NodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode.ExpressionKind;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.AssumeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CompoundStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ExpressionStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ForLoopInitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ForLoopNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ReturnNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.FunctionTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.util.IF.Triple;

//TODO: translate exit(k) to return k;
/**
 * MPI2CIVLTransformer transforms an AST of an MPI program into an AST of an
 * equivalent CIVL-C program. See {@linkplain #transform(AST)}. TODO: copy
 * output files only for the mpi process with rank 0.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class MPI2CIVLTransformer extends CIVLBaseTransformer {

	/* ************************** Public Static Fields *********************** */
	/**
	 * The code (short name) of this transformer.
	 */
	public final static String CODE = "mpi";

	/**
	 * The long name of the transformer.
	 */
	public final static String LONG_NAME = "MPITransformer";

	/**
	 * The description of this transformer.
	 */
	public final static String SHORT_DESCRIPTION = "transforms C/MPI program to CIVL-C";

	/* ************************** Private Static Fields ********************** */

	private static String EXIT = "exit";

	/**
	 * The name of the identifier of the MPI_Comm variable in the final CIVL
	 * program.
	 */
	private static String COMM_WORLD = "MPI_COMM_WORLD";

	private static String PTHREAD_POOL = "_pool";

	private static String PTHREAD_ADD_THREAD = "_add_thread";

	private static String PTHREAD_CREATE = "pthread_create";

	private static String PTHREAD_EXIT = "_pthread_exit";

	private static String PTHREAD_IS_TERMINATED = "_isTerminated";

	/**
	 * The name of the identifier of the CMPI_Gcomm variable in the final CIVL
	 * program.
	 */
	private static String GCOMM_WORLD = "GCOMM_WORLD";

	/**
	 * The name of CMPI_Gcomm type in the final CIVL-C program.
	 */
	private static String GCOMM_TYPE = "CMPI_Gcomm";

	/**
	 * The name of MPI_Comm type in both the original program and the final
	 * CIVL-C program.
	 */
	private static String COMM_TYPE = "MPI_Comm";

	/**
	 * The name of the function to create a new CMPI_Gcomm object in the final
	 * CIVL-C program.
	 */
	private static String GCOMM_CREATE = "CMPI_Gcomm_create";

	/**
	 * The name of the function to create a new MPI_Comm object in the final
	 * CIVL-C program.
	 */
	private static String COMM_CREATE = "CMPI_Comm_create";

	/**
	 * The name of the function to free a CMPI_Gcomm object in the final CIVL-C
	 * program.
	 */
	private static String GCOMM_DESTROY = "CMPI_Gcomm_destroy";

	/**
	 * The name of the function to free a MPI_Comm object in the final CIVL-C
	 * program.
	 */
	private static String COMM_DESTROY = "CMPI_Comm_destroy";

	/**
	 * The name used for renaming the main function of the original MPI program.
	 */
	private static String MPI_MAIN = "__main";

	/**
	 * The name of the parameter of a MPI procedure.
	 */
	private static String MPI_RANK = "__rank";

	/**
	 * The name of the function MPI_Init in the original MPI program.
	 */
	private static String MPI_INIT = "MPI_Init";

	/**
	 * The name of the function translating MPI_Init in the final CIVL-C
	 * program.
	 */
	private static String MPI_INIT_NEW = "__MPI_Init";

	/**
	 * The name of the function MPI_Init in the original MPI program.
	 */
	private static String MPI_FINALIZE = "MPI_Finalize";

	/**
	 * The name of the function translating MPI_Init in the final CIVL-C
	 * program.
	 */
	private static String MPI_FINALIZE_NEW = "__MPI_Finalize";

	/**
	 * The name of the variable representing the status of an MPI process, which
	 * is modified by MPI_Init() and MPI_Finalized().
	 */
	private static String MPI_STATUS = "__my_status";

	/**
	 * The name of the MPI procedure in the final CIVL-C program.
	 */
	private static String MPI_PROCESS = "MPI_Process";

	/**
	 * The name of the input variable denoting the number of MPI processes in
	 * the final CIVL-C program.
	 */
	private static String NPROCS = "__NPROCS";

	/**
	 * The name of the input variable denoting the upper bound of the number of
	 * MPI processes in the final CIVL-C program.
	 */
	private static String NPROCS_UPPER_BOUND = "__NPROCS_UPPER_BOUND";

	/**
	 * The name of the input variable denoting the lower bound of the number of
	 * MPI processes in the final CIVL-C program.
	 */
	private static String NPROCS_LOWER_BOUND = "__NPROCS_LOWER_BOUND";

	/**
	 * The name of the variable used to declare the array of references to all
	 * MPI processes in the final CIVL-C program.
	 */
	private static String PROCS = "__procs";

	/**
	 * The name of the function $wait() in the final CIVL-C program.
	 */
	private static String WAIT = "$wait";

	/**
	 * The name of $proc type in the final CIVL-C program.
	 */
	private static String PROC_TYPE = "$proc";

	/* **************************** Instant Fields ************************* */

	/**
	 * There are new nodes created by the transformer, other than parsing from
	 * some source file. All new nodes share the same source.
	 */
	private Source source;

	/* ****************************** Constructor ************************** */
	/**
	 * Creates a new instance of MPITransformer.
	 * 
	 * @param astFactory
	 *            The ASTFactory that will be used to create new nodes.
	 */
	public MPI2CIVLTransformer(ASTFactory astFactory,
			List<String> inputVariables, CIVLConfiguration config) {
		super(CODE, LONG_NAME, SHORT_DESCRIPTION, astFactory, inputVariables,
				config);
	}

	/* *************************** Private Methods ************************* */

	/**
	 * Creates a bound assumption node in the form of:
	 * <code>$assume lowerBound < variable && variable <= upperBound</code>.
	 * 
	 * @param lowerBound
	 *            The lower bound of the variable.
	 * @param variable
	 *            The variable to be bounded.
	 * @param upperBound
	 *            The upper bound of the variable.
	 * @return The node representing of the assumption on the bound of the
	 *         variable.
	 * @throws SyntaxException
	 */
	private AssumeNode boundAssumption(String lowerBound, String variable,
			String upperBound) throws SyntaxException {
		ExpressionNode variableExpression = this.identifierExpression(source,
				variable);
		ExpressionNode upperBoundExpression = this.identifierExpression(source,
				upperBound);
		ExpressionNode lowerBoundExpression = this.identifierExpression(source,
				lowerBound);
		ExpressionNode lowerPart, upperPart;

		lowerPart = nodeFactory.newOperatorNode(source, Operator.LT,
				Arrays.asList(lowerBoundExpression, variableExpression));
		variableExpression = variableExpression.copy();
		upperPart = nodeFactory.newOperatorNode(source, Operator.LTE,
				Arrays.asList(variableExpression, upperBoundExpression));
		return nodeFactory.newAssumeNode(
				source,
				nodeFactory.newOperatorNode(source, Operator.LAND,
						Arrays.asList(lowerPart, upperPart)));
	}

	/**
	 * Creates a bound assumption node in the form of:
	 * <code>$assume 0 < variable && variable <= upperBound</code>.
	 * 
	 * @param variable
	 *            The variable to be bounded.
	 * @param upperBound
	 *            The upper bound of the variable.
	 * @return The node representing of the assumption on the bound of the
	 *         variable.
	 * @throws SyntaxException
	 */
	private AssumeNode upperBoundAssumption(String variable, String upperBound)
			throws SyntaxException {
		ExpressionNode variableExpression = this.identifierExpression(source,
				variable);
		ExpressionNode upperBoundExpression = this.identifierExpression(source,
				upperBound);
		ExpressionNode lowerBoundExpression = nodeFactory
				.newIntegerConstantNode(source, "0");
		ExpressionNode lowerPart, upperPart;

		lowerPart = nodeFactory.newOperatorNode(source, Operator.LT,
				Arrays.asList(lowerBoundExpression, variableExpression));
		variableExpression = variableExpression.copy();
		upperPart = nodeFactory.newOperatorNode(source, Operator.LTE,
				Arrays.asList(variableExpression, upperBoundExpression));
		return nodeFactory.newAssumeNode(
				source,
				nodeFactory.newOperatorNode(source, Operator.LAND,
						Arrays.asList(lowerPart, upperPart)));
	}

	/**
	 * Creates the declaration node for the variable <code>MPI_COMM_WORLD</code>
	 * , which is of <code>MPI_Comm</code> type and has an initializer to call
	 * <code>$comm_create()</code>. That is:
	 * <code>MPI_Comm MPI_COMM_WORLD = $comm_create($here, GCOMM_WORLD, _rank)</code>
	 * .
	 * 
	 * @return The declaration node of the variable <code>MPI_COMM_WORLD</code>.
	 */
	private VariableDeclarationNode commDeclaration() {
		TypeNode commType;
		List<ExpressionNode> commCreateArgs;
		ExpressionNode commCreate;

		commType = nodeFactory.newTypedefNameNode(
				nodeFactory.newIdentifierNode(source, COMM_TYPE), null);
		commCreateArgs = new ArrayList<>(3);
		commCreateArgs.add(nodeFactory.newHereNode(source));
		commCreateArgs.add(this.identifierExpression(source, GCOMM_WORLD));
		commCreateArgs.add(this.identifierExpression(source, MPI_RANK));
		commCreate = nodeFactory.newFunctionCallNode(source,
				this.identifierExpression(source, COMM_CREATE), commCreateArgs,
				null);
		return nodeFactory.newVariableDeclarationNode(source,
				nodeFactory.newIdentifierNode(source, COMM_WORLD), commType,
				commCreate);
	}

	/**
	 * Creates an expression statement node of a function call node for
	 * destroying a communicator, either global or local.
	 * 
	 * @param destroy
	 *            The name of the function call, either
	 *            <code>$gcomm_destroy</code> or <code>$comm_destroy</code>.
	 * @param commName
	 *            The name of the variable of the communicator to be destroy,
	 *            either <code>GCOMM_WORLD</code> or <code>MPI_COMM_WORLD</code>
	 *            .
	 * @return The expression statement node of the function call for destroying
	 *         the specified communicator.
	 */
	private ExpressionStatementNode commDestroy(String destroy, String commName) {
		ExpressionNode function = this.identifierExpression(source, destroy);

		return nodeFactory.newExpressionStatementNode(nodeFactory
				.newFunctionCallNode(source, function, Arrays.asList(this
						.identifierExpression(source, commName)), null));
	}

	/**
	 * Creates the declaration node for the variable <code>GCOMM_WORLD</code> ,
	 * which is of <code>$gcomm</code> type and has an initializer to call
	 * <code>$gcomm_create()</code>. That is:
	 * <code>$gcomm GCOMM_WORLD = $gcomm_create($here, NPROCS)</code> .
	 * 
	 * @return The declaration node of the variable <code>GCOMM_WORLD</code>.
	 */
	private VariableDeclarationNode gcommDeclaration() {
		TypeNode gcommType;
		ExpressionNode gcommCreate;

		gcommType = nodeFactory.newTypedefNameNode(
				nodeFactory.newIdentifierNode(source, GCOMM_TYPE), null);
		gcommCreate = nodeFactory.newFunctionCallNode(
				source,
				this.identifierExpression(source, GCOMM_CREATE),
				Arrays.asList(nodeFactory.newHereNode(source),
						this.identifierExpression(source, NPROCS)), null);
		return nodeFactory.newVariableDeclarationNode(source,
				nodeFactory.newIdentifierNode(source, GCOMM_WORLD), gcommType,
				gcommCreate);
	}

	/**
	 * Creates the main function for the final program, which is: <br>
	 * 
	 * <pre>
	 * void main(){
	 *   $proc procs[NPROCS]; 
	 *   for(int i = 0; i < NPROCS; i++)
	 *     procs[i] = $spawn MPI_Process(i);
	 *   for(int i = 0; i < NPROCS; i++)
	 *     $wait(procs[i]);
	 *   $gcomm_destroy(GCOMM_WORLD);
	 * }
	 * </pre>
	 * 
	 * @return The function definition node representing the main function of
	 *         the final program.
	 * @throws SyntaxException
	 */
	private FunctionDefinitionNode mainFunction() throws SyntaxException {
		List<BlockItemNode> items = new LinkedList<BlockItemNode>();
		TypeNode procsType;
		VariableDeclarationNode procsVar;
		ForLoopInitializerNode initializerNode;
		ExpressionNode loopCondition, incrementer, spawnProc, waitProc, leftHandSide;
		StatementNode assign;
		ForLoopNode forLoop;
		CompoundStatementNode mainBody;
		SequenceNode<VariableDeclarationNode> formals;
		FunctionTypeNode mainType;
		FunctionDefinitionNode mainFunction;
		ExpressionStatementNode gcommDestroy = this.commDestroy(GCOMM_DESTROY,
				GCOMM_WORLD);

		// declaring $proc procs[NPROCS];
		procsType = nodeFactory
				.newArrayTypeNode(source,
						nodeFactory.newTypedefNameNode(nodeFactory
								.newIdentifierNode(source, PROC_TYPE), null),
						this.identifierExpression(source, NPROCS));
		procsVar = nodeFactory.newVariableDeclarationNode(source,
				nodeFactory.newIdentifierNode(source, PROCS), procsType);
		items.add(procsVar);
		// first for loop;
		initializerNode = nodeFactory
				.newForLoopInitializerNode(source,
						Arrays.asList(nodeFactory.newVariableDeclarationNode(
								source, nodeFactory.newIdentifierNode(source,
										"i"), nodeFactory.newBasicTypeNode(
										source, BasicTypeKind.INT), nodeFactory
										.newIntegerConstantNode(source, "0"))));
		loopCondition = nodeFactory.newOperatorNode(
				source,
				Operator.LT,
				Arrays.asList(this.identifierExpression(source, "i"),
						this.identifierExpression(source, NPROCS)));
		incrementer = nodeFactory.newOperatorNode(source,
				Operator.POSTINCREMENT,
				Arrays.asList(this.identifierExpression(source, "i")));
		spawnProc = nodeFactory.newSpawnNode(source, nodeFactory
				.newFunctionCallNode(source,
						this.identifierExpression(source, MPI_PROCESS),
						Arrays.asList(this.identifierExpression(source, "i")),
						null));
		leftHandSide = nodeFactory.newOperatorNode(
				source,
				Operator.SUBSCRIPT,
				Arrays.asList(this.identifierExpression(source, PROCS),
						this.identifierExpression(source, "i")));
		assign = nodeFactory.newExpressionStatementNode(nodeFactory
				.newOperatorNode(source, Operator.ASSIGN,
						Arrays.asList(leftHandSide, spawnProc)));
		forLoop = nodeFactory.newForLoopNode(source, initializerNode,
				loopCondition, incrementer, assign, null);
		items.add(forLoop);
		// second for loop;
		initializerNode = nodeFactory
				.newForLoopInitializerNode(source,
						Arrays.asList(nodeFactory.newVariableDeclarationNode(
								source, nodeFactory.newIdentifierNode(source,
										"i"), nodeFactory.newBasicTypeNode(
										source, BasicTypeKind.INT), nodeFactory
										.newIntegerConstantNode(source, "0"))));
		loopCondition = nodeFactory.newOperatorNode(
				source,
				Operator.LT,
				Arrays.asList(this.identifierExpression(source, "i"),
						this.identifierExpression(source, NPROCS)));
		incrementer = nodeFactory.newOperatorNode(source,
				Operator.POSTINCREMENT,
				Arrays.asList(this.identifierExpression(source, "i")));
		waitProc = nodeFactory
				.newFunctionCallNode(source, this.identifierExpression(source,
						WAIT),
						Arrays.asList((ExpressionNode) nodeFactory
								.newOperatorNode(source, Operator.SUBSCRIPT,
										Arrays.asList(this
												.identifierExpression(source,
														PROCS), this
												.identifierExpression(source,
														"i")))), null);
		forLoop = nodeFactory.newForLoopNode(source, initializerNode,
				loopCondition, incrementer,
				nodeFactory.newExpressionStatementNode(waitProc), null);
		items.add(forLoop);
		// destroying GCOMM_WROLD;
		items.add(gcommDestroy);
		// constructing the function definition node.
		mainBody = nodeFactory.newCompoundStatementNode(source, items);
		formals = nodeFactory.newSequenceNode(source,
				"FormalParameterDeclarations",
				new ArrayList<VariableDeclarationNode>());
		mainType = nodeFactory.newFunctionTypeNode(source,
				nodeFactory.newVoidTypeNode(source), formals, true);
		mainFunction = nodeFactory.newFunctionDefinitionNode(source,
				nodeFactory.newIdentifierNode(source, "main"), mainType, null,
				mainBody);
		return mainFunction;
	}

	/**
	 * 
	 * Constructs the function MPI_Process() from the original MPI program. It
	 * is a wrapper of the original MPI program with some additional features: <br>
	 * 
	 * <pre>
	 * void MPI_Process(){
	 *   $comm MPI_COMM_WORLD = $comm_create(...);
	 *   //SLIGHTLY-MODIFIED ORIGINAL PROGRAM;
	 *   int a, b, ...;
	 *   ... function(){...}
	 *   ...
	 *   ... __main(){...} // renamed main() to __main()
	 *   ....
	 *   //ORIGINAL PROGRAM ENDS HERE;
	 *   __main();
	 *   $comm_destroy(MPI_COMM_WORLD);
	 * }
	 * </pre>
	 * 
	 * @param root
	 *            The root node of the AST of the original MPI program.
	 * @return The function definition node of MPI_Process, the list of AST
	 *         nodes that are parsed from header files and will be moved up to
	 *         the higher scope (i.e., the file scope of the final AST), and the
	 *         list of variable declaration nodes that are the arguments of the
	 *         original main function which will be moved up to the higher scope
	 *         (i.e., the file scope of the final AST) and become $input
	 *         variables of the final AST.
	 */
	private Triple<FunctionDefinitionNode, List<ASTNode>, List<VariableDeclarationNode>> mpiProcess(
			SequenceNode<ASTNode> root) {
		List<ASTNode> includedNodes = new ArrayList<>();
		List<VariableDeclarationNode> vars = new ArrayList<>();
		List<BlockItemNode> items;
		int number;
		ExpressionStatementNode callMain;
		CompoundStatementNode mpiProcessBody;
		SequenceNode<VariableDeclarationNode> formals;
		FunctionTypeNode mpiProcessType;
		FunctionDefinitionNode mpiProcess;
		VariableDeclarationNode commVar = this.commDeclaration();
		ExpressionStatementNode commDestroy = this.commDestroy(COMM_DESTROY,
				COMM_WORLD);

		callMain = nodeFactory.newExpressionStatementNode(nodeFactory
				.newFunctionCallNode(source,
						this.identifierExpression(source, MPI_MAIN),
						new ArrayList<ExpressionNode>(), null));
		// build MPI_Process() function:
		items = new LinkedList<>();
		number = root.numChildren();
		items.add(commVar);
		for (int i = 0; i < number; i++) {
			ASTNode child = root.child(i);
			String sourceFile;

			if (child == null)
				continue;
			sourceFile = child.getSource().getFirstToken().getSourceFile()
					.getName();
			root.removeChild(i);
			if (sourceFile.equals("mpi.cvl")) {
				if (child.nodeKind() == NodeKind.VARIABLE_DECLARATION) {
					VariableDeclarationNode variableDeclaration = (VariableDeclarationNode) child;

					if (variableDeclaration.getName().equals(MPI_STATUS))
						// keep variable declaration node of __MPI_Status__
						// __my_status = __UNINIT;
						items.add(variableDeclaration);
					else
						includedNodes.add(child);
				} else
					includedNodes.add(child);
			} else if (sourceFile.equals("stdio.cvl")
					|| sourceFile.equals("pthread.cvl"))
				includedNodes.add(child);
			else if (sourceFile.equals("pthread-c.cvl")) {
				if (child.nodeKind() == NodeKind.VARIABLE_DECLARATION) {
					VariableDeclarationNode variableDeclaration = (VariableDeclarationNode) child;
					String varName = variableDeclaration.getName();

					if (varName.equals(PTHREAD_POOL))
						// keep variable declaration nodes for _pool in
						// pthread.cvl
						items.add(variableDeclaration);
					else
						includedNodes.add(child);
				} else if (child.nodeKind() == NodeKind.FUNCTION_DEFINITION) {
					FunctionDefinitionNode functionDef = (FunctionDefinitionNode) child;
					String name = functionDef.getName();

					if (name.equals(PTHREAD_ADD_THREAD)
							|| name.equals(PTHREAD_IS_TERMINATED)
							|| name.equals(PTHREAD_CREATE)
							|| name.equals(PTHREAD_EXIT))
						items.add(functionDef);
					else
						includedNodes.add(child);
				} else
					includedNodes.add(child);
			} else if (sourceFile.endsWith(".h")) {
				if (child.nodeKind() == NodeKind.VARIABLE_DECLARATION) {
					VariableDeclarationNode variableDeclaration = (VariableDeclarationNode) child;

					if (sourceFile.equals("stdio.h"))
						// keep variable declaration nodes from stdio, i.e.,
						// stdout, stdin, etc.
						items.add(variableDeclaration);
					else if (!variableDeclaration.getName().equals(COMM_WORLD))
						// ignore the MPI_COMM_WORLD declaration in mpi.h.
						includedNodes.add(child);
				} else
					includedNodes.add(child);
			} else {
				if (child.nodeKind() == NodeKind.VARIABLE_DECLARATION) {
					VariableDeclarationNode variable = (VariableDeclarationNode) child;

					if (variable.getTypeNode().isInputQualified()
							|| variable.getTypeNode().isOutputQualified()) {
						vars.add(variable);
						continue;
					}
				}
				if (child.nodeKind() == NodeKind.FUNCTION_DEFINITION) {
					FunctionDefinitionNode functionNode = (FunctionDefinitionNode) child;
					IdentifierNode functionName = (IdentifierNode) functionNode
							.child(0);

					if (functionName.name().equals("main"))
						functionName.setName(MPI_MAIN);
				}
				items.add((BlockItemNode) child);
			}
		}
		items.add(callMain);
		items.add(commDestroy);
		mpiProcessBody = nodeFactory.newCompoundStatementNode(root.getSource(),
				items);
		formals = nodeFactory
				.newSequenceNode(source, "FormalParameterDeclarations", Arrays
						.asList(nodeFactory
								.newVariableDeclarationNode(source, nodeFactory
										.newIdentifierNode(source, MPI_RANK),
										nodeFactory.newBasicTypeNode(source,
												BasicTypeKind.INT))));
		mpiProcessType = nodeFactory.newFunctionTypeNode(source,
				nodeFactory.newVoidTypeNode(source), formals, true);
		mpiProcess = nodeFactory.newFunctionDefinitionNode(source,
				nodeFactory.newIdentifierNode(source, MPI_PROCESS),
				mpiProcessType, null, mpiProcessBody);
		return new Triple<>(mpiProcess, includedNodes, vars);
	}

	/**
	 * Declare a variable of a basic type with a specific name.
	 * 
	 * @param type
	 *            The kind of basic type.
	 * @param name
	 *            The name of the variable.
	 * @return The variable declaration node.
	 */
	private VariableDeclarationNode basicTypeVariableDeclaration(
			BasicTypeKind type, String name) {
		TypeNode typeNode = nodeFactory.newBasicTypeNode(source, type);

		return nodeFactory.newVariableDeclarationNode(source,
				nodeFactory.newIdentifierNode(source, name), typeNode);
	}

	/**
	 * Creates the declaration node for the input variable <code>NPROCS</code>.
	 * 
	 * @return The declaration node of the input variable <code>NPROCS</code>.
	 */
	private VariableDeclarationNode nprocsDeclaration() {
		TypeNode nprocsType = nodeFactory.newBasicTypeNode(source,
				BasicTypeKind.INT);

		nprocsType.setInputQualified(true);
		return nodeFactory.newVariableDeclarationNode(source,
				nodeFactory.newIdentifierNode(source, NPROCS), nprocsType);
	}

	/**
	 * Scans all children nodes to do preprocessing. Currently, only one kind of
	 * processing is performed, i.e., translating all <code>MPI_Init(...)</code>
	 * function call into <code>__MPI_Init()</code>.
	 * 
	 * @param node
	 *            The AST node to be checked and all its children will be
	 *            scanned.
	 * @throws SyntaxException
	 */
	private void preprocessASTNode(ASTNode node) throws SyntaxException {
		int numChildren = node.numChildren();

		for (int i = 0; i < numChildren; i++) {
			ASTNode child = node.child(i);

			if (child != null)
				this.preprocessASTNode(node.child(i));
		}
		if (node instanceof FunctionCallNode) {
			this.preprocessFunctionCall((FunctionCallNode) node);
		}

	}

	/**
	 * 
	 * Translates an <code>MPI_Init(...)</code> function call into
	 * <code>__MPI_Init(MPI_COMM_WORLD)</code>.
	 * 
	 * 
	 * @param functionCall
	 */
	private void preprocessFunctionCall(FunctionCallNode functionCall) {
		if (functionCall.getFunction().expressionKind() == ExpressionKind.IDENTIFIER_EXPRESSION) {
			IdentifierExpressionNode functionExpression = (IdentifierExpressionNode) functionCall
					.getFunction();
			String functionName = functionExpression.getIdentifier().name();

			if (functionName.equals(MPI_INIT)) {
				ExpressionNode addressOf = nodeFactory.newOperatorNode(source,
						Operator.ADDRESSOF, Arrays.asList(this
								.identifierExpression(source, COMM_WORLD)));

				functionExpression.getIdentifier().setName(MPI_INIT_NEW);
				functionCall.setArguments(nodeFactory.newSequenceNode(source,
						"ActualParameterList", Arrays.asList(addressOf)));
			} else if (functionName.equals(MPI_FINALIZE)) {
				ExpressionNode addressOf = nodeFactory.newOperatorNode(source,
						Operator.ADDRESSOF, Arrays.asList(this
								.identifierExpression(source, COMM_WORLD)));

				functionExpression.getIdentifier().setName(MPI_FINALIZE_NEW);
				functionCall.setArguments(nodeFactory.newSequenceNode(source,
						"ActualParameterList", Arrays.asList(addressOf)));
			} else if (functionName.equals(EXIT)) {
				int myIndex = functionCall.parent().childIndex();
				ExpressionNode value = functionCall.getArgument(0).copy();
				ReturnNode returnNode = nodeFactory
						.newReturnNode(source, value);
				ASTNode parent = functionCall.parent().parent();

				parent.setChild(myIndex, returnNode);
			}
		}
	}

	/**
	 * Creates the assumption node for NPROCS.
	 * 
	 * @return the assumption node of NPROCS, null if the input variable list
	 *         already contains NPROCS.
	 * @throws SyntaxException
	 */
	private AssumeNode nprocsAssumption() throws SyntaxException {
		if (this.inputVariableNames.contains(NPROCS))
			return null;
		if (this.inputVariableNames.contains(NPROCS_LOWER_BOUND))
			return this.boundAssumption(NPROCS_LOWER_BOUND, NPROCS,
					NPROCS_UPPER_BOUND);
		return upperBoundAssumption(NPROCS, NPROCS_UPPER_BOUND);
	}

	/* ********************* Methods From BaseTransformer ****************** */

	/**
	 * Transform an AST of a pure MPI program in C into an equivalent AST of
	 * CIVL-C program.<br>
	 * Given an MPI program:<br>
	 * 
	 * <pre>
	 * #include &lt;mpi.h>
	 * ...
	 * #include &lt;stdio.h>
	 * int a, b, ...;
	 * ... function(){
	 *   ...
	 * }
	 * ...
	 * int main(){
	 *   ....
	 * }
	 * </pre>
	 * 
	 * It is translated to the following program:<br>
	 * 
	 * <pre>
	 * #include &lt;mpi.h> // all included files are moved above to the new file scope.
	 * ...
	 * #include &lt;stdio.h>
	 * $input int argc;//optional, only necessary when the original main function has arguments.
	 * $input char** argv;//optional, only necessary when the original main function has arguments.
	 * $input int NPROCS;
	 * $gcomm GCOMM_WORLD = $gcomm_create($here, NPROCS);
	 * 
	 * void MPI_Process(int _rank){
	 *   ...
	 * }
	 * void main(){
	 *   $proc procs[NPROCS];
	 *   for(int i = 0; i < NPROCS; i++)
	 *     procs[i] = $spawn MPI_Process(i);
	 *   for(int i = 0; i < NPROCS; i++)
	 *     $wait(procs[i]);
	 *   $gcomm_destroy(GCOMM_WORLD);
	 * }
	 * </pre>
	 * 
	 * Whereas MPI_Process() is a wrapper of the original MPI program with some
	 * special handling:<br>
	 * 
	 * <pre>
	 * void MPI_Process(){
	 *   $comm MPI_COMM_WORLD = $comm_create(...);
	 *   //SLIGHTLY-MODIFIED ORIGINAL PROGRAM;
	 *   int a, b, ...;
	 *   ... function(){...}
	 *   ...
	 *   ... __main(){...} // renamed main() to __main()
	 *   ....
	 *   //ORIGINAL PROGRAM ENDS HERE;
	 *   __main();
	 *   $comm_destroy(MPI_COMM_WORLD);
	 * }
	 * </pre>
	 * 
	 * @param ast
	 *            The AST of the original MPI program in C.
	 * @return An AST of CIVL-C program equivalent to the original MPI program.
	 * @throws SyntaxException
	 */
	@SuppressWarnings("unchecked")
	@Override
	public AST transform(AST ast) throws SyntaxException {
		ASTNode root = ast.getRootNode();
		AST newAst;
		FunctionDefinitionNode mpiProcess, mainFunction;
		VariableDeclarationNode gcommWorld;
		List<ASTNode> externalList;
		VariableDeclarationNode nprocsVar;
		VariableDeclarationNode nprocsUpperBoundVar = null, nprocsLowerBoundVar = null;
		SequenceNode<ASTNode> newRootNode;
		List<ASTNode> includedNodes = new ArrayList<ASTNode>();
		List<VariableDeclarationNode> mainParameters = new ArrayList<>();
		int count;
		AssumeNode nprocsAssumption = null;
		Triple<FunctionDefinitionNode, List<ASTNode>, List<VariableDeclarationNode>> result;

		this.source = getMainSource(root);// TODO needs a good source
		assert this.astFactory == ast.getASTFactory();
		assert this.nodeFactory == astFactory.getNodeFactory();
		ast.release();
		// change MPI_Init(...) to _MPI_Init();
		preprocessASTNode(root);
		// declaring $input int NPROCS;
		nprocsVar = this.nprocsDeclaration();
		// declaring $input int NPROCS_UPPER_BOUND;
		if (!this.inputVariableNames.contains(NPROCS)
				&& this.inputVariableNames.contains(NPROCS_UPPER_BOUND)) {
			nprocsUpperBoundVar = this.basicTypeVariableDeclaration(
					BasicTypeKind.INT, NPROCS_UPPER_BOUND);
			nprocsUpperBoundVar.getTypeNode().setInputQualified(true);
		}
		if (!this.inputVariableNames.contains(NPROCS)
				&& this.inputVariableNames.contains(NPROCS_LOWER_BOUND)) {
			// declaring $input int NPROCS_LOWER_BOUND;
			nprocsLowerBoundVar = this.basicTypeVariableDeclaration(
					BasicTypeKind.INT, NPROCS_LOWER_BOUND);
			nprocsLowerBoundVar.getTypeNode().setInputQualified(true);
		}
		if (!this.inputVariableNames.contains(NPROCS)
				&& !this.inputVariableNames.contains(NPROCS_UPPER_BOUND)) {
			throw new SyntaxException(
					"Please specify the number of processes (e.g., -input__NPROCS=5)"
							+ "or the upper bound of number of processes (e.g. -input__NPROCS_UPPER_BOUND=6)",
					source);// TODO improve messages with pragma.
		}
		// assuming NPROCS_LOWER_BOUND < NPROCS && NPROCS <= NPROCS_UPPER_BOUND
		nprocsAssumption = this.nprocsAssumption();
		// declaring $gcomm GCOMM_WORLD = $gcomm_create($here, NPROCS);
		gcommWorld = this.gcommDeclaration();
		result = this.mpiProcess((SequenceNode<ASTNode>) root);
		mpiProcess = result.first;
		includedNodes = result.second;
		mainParameters = result.third;
		// defining the main function;
		mainFunction = mainFunction();
		// the translated program is:
		// input variables;
		// gcomm
		// MPI_Process() definition;
		// main function.
		externalList = new LinkedList<>();
		count = includedNodes.size();
		// adding nodes from header files.
		for (int i = 0; i < count; i++) {
			externalList.add(includedNodes.get(i));
		}
		count = mainParameters.size();
		// adding nodes from the arguments of the original main function.
		for (int i = 0; i < count; i++) {
			externalList.add(mainParameters.get(i));
		}
		externalList.add(nprocsVar);
		if (nprocsLowerBoundVar != null)
			externalList.add(nprocsLowerBoundVar);
		if (nprocsUpperBoundVar != null)
			externalList.add(nprocsUpperBoundVar);
		if (nprocsAssumption != null)
			externalList.add(nprocsAssumption);
		externalList.add(gcommWorld);
		externalList.add(mpiProcess);
		externalList.add(mainFunction);
		newRootNode = nodeFactory.newSequenceNode(null, "TranslationUnit",
				externalList);
		newAst = astFactory.newAST(newRootNode);
		return newAst;
	}

}
