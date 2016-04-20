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
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CompoundStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.DeclarationListNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ExpressionStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.FunctionTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.parse.IF.CParser;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.civl.config.IF.CIVLConstants;
import edu.udel.cis.vsl.civl.util.IF.Triple;

//TODO: added CMPI_destroy call before each call to exit(k);
/**
 * MPI2CIVLTransformer transforms an AST of an MPI program into an AST of an
 * equivalent CIVL-C program. See {@linkplain #transform(AST)}. TODO: copy
 * output files only for the mpi process with rank 0.
 * 
 * 
 * The MPI transformer tries to move the main function and file scope stuffs of
 * the original MPI program into the scope of the function MPI_Process(). Most
 * unstateful functions remain in the file scope, which are usually functions of
 * included headers. The Pthread library implementation contains a global
 * variable for the thread pool, which however, if in a MPI+Pthread program,
 * should go to the scope of the MPI process, instead of the file scope. And
 * ditto for pthread_create, pthread_exit, pthread_is_terminated function,
 * because they access the thread pool.
 * 
 * CIVL currently uses this order for transformers: general, IO, OpenMP,
 * Pthread, CUDA, MPI.
 * 
 * At this point, the order matters. Because if MPI transformer goes first,
 * Pthread transformer is not be able to insert the thread pool variable in the
 * right place. Since MPI is modifying the program structure more than other
 * transformers (moving the original file scope stuffs to a function), it is
 * easier to make it always the last transformer to apply.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class MPI2CIVLWorker extends BaseWorker {

	/* ************************** Pthread Constants ********************** */

	private static final String PTHREAD_JOIN = "pthread_join";
	private static final String PTHREAD_PTR = "value_ptr_value";

	/* ************************** Private Static Fields ********************** */

	private final static String EXIT = "exit";
	private final static String MPI_PREFIX = "_mpi_";

	/**
	 * The name of the identifier of the MPI_Comm variable in the final CIVL
	 * program.
	 */
	private final static String COMM_WORLD = "MPI_COMM_WORLD";

	/**
	 * The name of the identifier of the CMPI_Gcomm variable in the final CIVL
	 * program.
	 */
	private final static String GCOMM_WORLD = "_mpi_gcomm";

	/**
	 * The name of the identifier of the CMPI_Gcomm sequence variable in the
	 * final CIVL-MPI program
	 */
	private final static String GCOMMS = "_mpi_gcomms";

	/**
	 * The name of the function call for initializing a sequence.
	 */
	private final static String SEQ_INIT = "$seq_init";

	/**
	 * The name of CMPI_Gcomm type in the final CIVL-C program.
	 */
	private final static String GCOMM_TYPE = "$mpi_gcomm";

	/**
	 * The name of MPI_Comm type in both the original program and the final
	 * CIVL-C program.
	 */
	private final static String COMM_TYPE = "MPI_Comm";

	/**
	 * The name of the function to create a new CMPI_Gcomm object in the final
	 * CIVL-C program.
	 */
	private final static String GCOMM_CREATE = "$mpi_gcomm_create";

	/**
	 * The name of the function to create a new MPI_Comm object in the final
	 * CIVL-C program.
	 */
	private final static String COMM_CREATE = "$mpi_comm_create";

	/**
	 * The name of the function to free a CMPI_Gcomm object in the final CIVL-C
	 * program.
	 */
	private final static String GCOMM_DESTROY = "$mpi_gcomm_destroy";

	/**
	 * The name of the function to free a MPI_Comm object in the final CIVL-C
	 * program.
	 */
	private final static String COMM_DESTROY = "$mpi_comm_destroy";

	/**
	 * The name of the parameter of a MPI procedure.
	 */
	private final String MPI_RANK = MPI_PREFIX + "rank";

	/**
	 * The name of the function MPI_Init in the original MPI program.
	 */
	private final static String MPI_INIT = "MPI_Init";

	/**
	 * The name of the function translating MPI_Init in the final CIVL-C
	 * program.
	 */
	private final static String MPI_INIT_NEW = "$mpi_init";

	/**
	 * The name of the function MPI_Init in the original MPI program.
	 */
	private final static String MPI_FINALIZE = "MPI_Finalize";

	/**
	 * The name of the function translating MPI_Init in the final CIVL-C
	 * program.
	 */
	private final static String MPI_FINALIZE_NEW = "$mpi_finalize";

	/**
	 * The name of the variable representing the status of an MPI process, which
	 * is modified by MPI_Init() and MPI_Finalized().
	 */
	private final static String MPI_SYS_STATUS = "_mpi_status";

	/**
	 * The name of the type of variables representing the status of an MPI
	 * process.
	 */
	private final static String MPI_SYS_STATUS_TYPENAME = "$mpi_sys_status";

	/**
	 * The name of the MPI procedure in the final CIVL-C program.
	 */
	private final static String MPI_PROCESS = "_mpi_process";

	/**
	 * The name of the input variable denoting the number of MPI processes in
	 * the final CIVL-C program.
	 */
	private final static String NPROCS = "_mpi_nprocs";

	/**
	 * The name of the input variable denoting the upper bound of the number of
	 * MPI processes in the final CIVL-C program.
	 */
	private final static String NPROCS_UPPER_BOUND = "_mpi_nprocs_hi";

	/**
	 * The name of the input variable denoting the lower bound of the number of
	 * MPI processes in the final CIVL-C program.
	 */
	private final static String NPROCS_LOWER_BOUND = "_mpi_nprocs_lo";

	/* ****************************** Constructor ************************** */
	/**
	 * Creates a new instance of MPITransformer.
	 * 
	 * @param astFactory
	 *            The ASTFactory that will be used to create new nodes.
	 */
	public MPI2CIVLWorker(ASTFactory astFactory) {
		super("MPItoCIVLTransformer", astFactory);
		this.identifierPrefix = MPI_PREFIX;
	}

	/* *************************** Private Methods ************************* */

	// /**
	// * Checks the stdio transformer status of a given AST. Specifically, this
	// * method checks if the any of the varaibles stdout, stdin and stderr are
	// * present and store the result to
	// *
	// * @param root
	// */
	// private void checkStdioStatus(ASTNode root) {
	// }

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
	private ExpressionStatementNode boundAssumption(String lowerBound,
			String variable, String upperBound) throws SyntaxException {
		ExpressionNode variableExpression = this.identifierExpression(variable);
		ExpressionNode upperBoundExpression = this
				.identifierExpression(upperBound);
		ExpressionNode lowerBoundExpression = this
				.identifierExpression(lowerBound);
		ExpressionNode lowerPart, upperPart;
		Source source = this.newSource("assumption on the bound of variable "
				+ variable, CParser.EXPRESSION_STATEMENT);

		lowerPart = nodeFactory.newOperatorNode(this.newSource(
				"lower bound of variable " + variable, CParser.EXPR),
				Operator.LTE, Arrays.asList(lowerBoundExpression,
						variableExpression));
		variableExpression = variableExpression.copy();
		upperPart = nodeFactory.newOperatorNode(this.newSource(
				"upper bound of variable " + variable, CParser.EXPR),
				Operator.LTE, Arrays.asList(variableExpression,
						upperBoundExpression));
		return nodeFactory.newExpressionStatementNode(this.functionCall(source,
				ASSUME, Arrays.asList((ExpressionNode) nodeFactory
						.newOperatorNode(
								this.newSource("logical and ", CParser.EXPR),
								Operator.LAND,
								Arrays.asList(lowerPart, upperPart)))));
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

		commType = nodeFactory.newTypedefNameNode(nodeFactory
				.newIdentifierNode(
						this.newSource("$comm type", CParser.IDENTIFIER),
						COMM_TYPE), null);
		commCreateArgs = new ArrayList<>(3);
		commCreateArgs.add(this.hereNode());
		commCreateArgs.add(this.identifierExpression(GCOMM_WORLD));
		commCreateArgs.add(this.identifierExpression(MPI_RANK));
		commCreate = nodeFactory.newFunctionCallNode(
				this.newSource("function call " + COMM_CREATE, CParser.CALL),
				this.identifierExpression(COMM_CREATE), commCreateArgs, null);
		return this.variableDeclaration(COMM_WORLD, commType, commCreate);
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
		ExpressionNode function = this.identifierExpression(destroy);

		return nodeFactory.newExpressionStatementNode(nodeFactory
				.newFunctionCallNode(this.newSource("function call " + destroy,
						CParser.CALL), function, Arrays.asList(this
						.identifierExpression(commName)), null));
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

		gcommType = nodeFactory.newTypedefNameNode(this.identifier(GCOMM_TYPE),
				null);
		gcommCreate = nodeFactory.newFunctionCallNode(
				this.newSource("function call " + GCOMM_CREATE, CParser.CALL),
				this.identifierExpression(GCOMM_CREATE),
				Arrays.asList(this.hereNode(),
						this.identifierExpression(NPROCS)), null);
		return this.variableDeclaration(GCOMM_WORLD, gcommType, gcommCreate);
	}

	// TODO: doc
	private VariableDeclarationNode gcommsSeqDeclaration() {
		TypeNode gcommType, gcommArrayType;
		VariableDeclarationNode node;

		gcommType = nodeFactory.newTypedefNameNode(this.identifier(GCOMM_TYPE),
				null);
		gcommArrayType = nodeFactory.newArrayTypeNode((Source) null, gcommType,
				null);
		node = this.variableDeclaration(GCOMMS, gcommArrayType, null);
		return node;
	}

	private ExpressionStatementNode gcommsSeqInitCalling()
			throws SyntaxException {
		FunctionCallNode node;
		OperatorNode gcommsPtrNode, gcommworldPtrNode;

		gcommsPtrNode = nodeFactory.newOperatorNode(
				this.newSource("&", CParser.OPERATOR), Operator.ADDRESSOF,
				this.identifierExpression(GCOMMS));
		gcommworldPtrNode = nodeFactory.newOperatorNode(
				this.newSource("&", CParser.OPERATOR), Operator.ADDRESSOF,
				this.identifierExpression(GCOMM_WORLD));
		node = nodeFactory.newFunctionCallNode(this.newSource("function call "
				+ SEQ_INIT, CParser.CALL), this.identifierExpression(SEQ_INIT),
				Arrays.asList(gcommsPtrNode,
						nodeFactory.newIntegerConstantNode(null, "1"),
						gcommworldPtrNode), null);
		return nodeFactory.newExpressionStatementNode(node);
	}

	// private ExpressionStatementNode elaborateNPROCS() {
	// FunctionCallNode elaborateCall = nodeFactory.newFunctionCallNode(
	// this.newSource("elaborate _NPROCS", CParser.CALL),
	// this.identifierExpression("$elaborate"),
	// Arrays.asList(this.identifierExpression(NPROCS)), null);
	//
	// return nodeFactory.newExpressionStatementNode(elaborateCall);
	// }

	/**
	 * Creates the main function for the final program, which is: <br>
	 * 
	 * <pre>
	 * void main(){
	 *   for(int i = 0; i &lt; 10; i++)
	 *     _argv[i]=&CIVL_argv[i][0];
	 *   $parfor(int i: 0 .. NPROCS-1)
	 *     MPI_Process(i);
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
		DeclarationListNode iterator;
		ExpressionNode upperBound;
		CompoundStatementNode mainBody;
		SequenceNode<VariableDeclarationNode> formals;
		FunctionTypeNode mainType;
		FunctionDefinitionNode mainFunction;
		ExpressionStatementNode gcommDestroy = this.commDestroy(GCOMM_DESTROY,
				GCOMM_WORLD);
		ExpressionNode domain;
		FunctionCallNode callMPIprocess;
		StatementNode parforMPIproc;

		iterator = nodeFactory
				.newForLoopInitializerNode(
						newSource("$parfor loop variable",
								CParser.INIT_DECLARATOR_LIST), Arrays
								.asList(this.variableDeclaration("i",
										this.basicType(BasicTypeKind.INT))));
		upperBound = nodeFactory.newOperatorNode(
				this.newSource("post increment", CParser.POST_INCREMENT),
				Operator.MINUS,
				Arrays.asList(this.identifierExpression(NPROCS),
						this.integerConstant(1)));
		domain = nodeFactory.newRegularRangeNode(
				this.newSource("regular range", CParser.RANGE),
				this.integerConstant(0), upperBound);
		callMPIprocess = nodeFactory.newFunctionCallNode(
				this.newSource("function call " + MPI_PROCESS, CParser.CALL),
				this.identifierExpression(MPI_PROCESS),
				Arrays.asList(this.identifierExpression("i")), null);
		parforMPIproc = nodeFactory.newCivlForNode(
				this.newSource("$parfor MPI_Process", CParser.PARFOR), true,
				iterator, domain,
				nodeFactory.newExpressionStatementNode(callMPIprocess), null);
		// items.add(this.elaborateNPROCS());
		items.add(parforMPIproc);
		// destroying GCOMM_WROLD;
		items.add(gcommDestroy);
		// constructing the function definition node.
		mainBody = nodeFactory.newCompoundStatementNode(
				this.newSource("main body", CParser.COMPOUND_STATEMENT), items);
		formals = nodeFactory.newSequenceNode(this.newSource(
				"formal parameter of the declaration of the main function",
				CParser.DECLARATION_LIST), "FormalParameterDeclarations",
				new ArrayList<VariableDeclarationNode>());
		mainType = nodeFactory.newFunctionTypeNode(
				this.newSource("type of the main function", CParser.TYPE),
				this.basicType(BasicTypeKind.INT), formals, true);
		mainFunction = nodeFactory.newFunctionDefinitionNode(
				this.newSource("definition of the main function",
						CParser.FUNCTION_DEFINITION), this.identifier("main"),
				mainType, null, mainBody);
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
	private Triple<FunctionDefinitionNode, List<BlockItemNode>, List<VariableDeclarationNode>> mpiProcess(
			SequenceNode<BlockItemNode> root) {
		List<BlockItemNode> includedNodes = new ArrayList<>();
		List<VariableDeclarationNode> vars = new ArrayList<>();
		List<BlockItemNode> items;
		int number;
		CompoundStatementNode mpiProcessBody;
		SequenceNode<VariableDeclarationNode> formals;
		FunctionTypeNode mpiProcessType;
		FunctionDefinitionNode mpiProcess;
		VariableDeclarationNode commVar = this.commDeclaration();
		ExpressionStatementNode commDestroy = this.commDestroy(COMM_DESTROY,
				COMM_WORLD);

		// build MPI_Process() function:
		items = new LinkedList<>();
		number = root.numChildren();
		// add MPI_Sys_status variable into each process
		items.add(mpiSysStatusDeclaration());
		items.add(mpiStatusDePruneAssertion());
		items.add(commVar);
		for (int i = 0; i < number; i++) {
			BlockItemNode child = root.getSequenceChild(i);
			String sourceFile;

			if (child == null)
				continue;
			sourceFile = child.getSource().getFirstToken().getSourceFile()
					.getName();
			root.removeChild(i);
			if (sourceFile.equals("mpi.cvl")) {
				if (child.nodeKind() == NodeKind.VARIABLE_DECLARATION) {
					VariableDeclarationNode variableDeclaration = (VariableDeclarationNode) child;

					if (variableDeclaration.getName().equals(MPI_SYS_STATUS))
						// keep variable declaration node of __MPI_Status__
						// __my_status = __UNINIT;
						items.add(variableDeclaration);
					else
						includedNodes.add(child);
				} else
					includedNodes.add(child);
			} else if (sourceFile.equals("pthread.cvl")) {
				// extern void *value_ptr_value = NULL;
				// extern $scope root = $here;
				// pthread_t * pool[];

				if (child.nodeKind() == NodeKind.VARIABLE_DECLARATION) {
					VariableDeclarationNode variableDeclaration = (VariableDeclarationNode) child;
					String varName = variableDeclaration.getName();

					if (varName.equals(Pthread2CIVLWorker.PTHREAD_GPOOL)
					// || varName.equals(PTHREAD_ROOT)
							|| varName.equals(PTHREAD_PTR))
						// keep variable declaration nodes for _pool in
						// pthread.cvl
						items.add(variableDeclaration);
					else
						includedNodes.add(child);
				} else if (child.nodeKind() == NodeKind.FUNCTION_DEFINITION) {
					FunctionDefinitionNode functionDef = (FunctionDefinitionNode) child;
					String name = functionDef.getName();

					if (name.equals(Pthread2CIVLWorker.PTHREAD_EXIT_MAIN_NEW)
							|| name.equals(PTHREAD_JOIN)
							|| name.equals(Pthread2CIVLWorker.PTHREAD_CREATE)
							|| name.equals(Pthread2CIVLWorker.PTHREAD_EXIT_NEW))
						// // ||
						// name.equals(Pthread2CIVLWorker.PTHREAD_MUTEX_LOCK))
						// || name.equals(PTHREAD_MUTEX_UNLOCK)
						// || name.equals(PTHREAD_MUTEX_TRYLOCK)
						// || name.equals(PTHREAD_COND_WAIT))
						items.add(functionDef);
					else
						includedNodes.add(child);
				} else
					includedNodes.add(child);
			} else if (sourceFile.equals("stdio.h")) {
				// ignore the variable declaration in stdio.h
				if (child.nodeKind() != NodeKind.VARIABLE_DECLARATION)
					includedNodes.add(child);
			} else if (sourceFile.equals("stdio.cvl")) {
				// keep variable declaration nodes from stdio.cvl, i.e.,
				// stdout, stdin, stderr, etc.
				if (child.nodeKind() == NodeKind.VARIABLE_DECLARATION) {
					VariableDeclarationNode varDecl = (VariableDeclarationNode) child;

					varDecl.setExternStorage(false);
					items.add(varDecl);
				} else
					includedNodes.add(child);
			} else if (sourceFile.equals("mpi.h")) {
				if (child.nodeKind() == NodeKind.VARIABLE_DECLARATION) {
					VariableDeclarationNode variableDeclaration = (VariableDeclarationNode) child;

					// ignore the MPI_COMM_WORLD declaration in mpi.h.
					if (!variableDeclaration.getName().equals(COMM_WORLD))
						includedNodes.add(child);
				} else
					includedNodes.add(child);
			} else if (CIVLConstants.getAllCLibraries().contains(sourceFile)) {// sourceFile.endsWith(".h"))
																				// {
				includedNodes.add(child);
			} else if (sourceFile.endsWith(".cvh")
					|| sourceFile.equals("civl-cuda.cvl")
					|| sourceFile.equals("civl-mpi.cvl")
					|| sourceFile.equals("civl-omp.cvl")
					|| sourceFile.equals("civl-pthread.cvl")
					|| sourceFile.equals("civlc.cvl")
					|| sourceFile.equals("comm.cvl")
					|| sourceFile.equals("concurrency.cvl")
					|| sourceFile.equals("cuda.cvl")
					|| sourceFile.equals("math.cvl")
					|| sourceFile.equals("mpi.cvl")
					|| sourceFile.equals("omp.cvl")
					|| sourceFile.equals("pthread-functions.cvl")
					|| sourceFile.equals("pthread-types.cvl")
					|| sourceFile.equals("sched.cvl")
					|| sourceFile.equals("seq.cvl")
					|| sourceFile.equals("stdio.cvl")

					|| sourceFile.equals("string.cvl")) {
				includedNodes.add(child);
			} else {
				if (child.nodeKind() == NodeKind.VARIABLE_DECLARATION) {
					VariableDeclarationNode variable = (VariableDeclarationNode) child;

					if (variable.getTypeNode().isInputQualified()
							|| variable.getTypeNode().isOutputQualified()
							|| (sourceFile.equals(GeneralWorker.NAME) && variable
									.getName().equals(GeneralWorker._argvName))) {
						vars.add(variable);
						continue;
					}
				}
				if (child.nodeKind() == NodeKind.FUNCTION_DEFINITION) {
					FunctionDefinitionNode functionNode = (FunctionDefinitionNode) child;
					IdentifierNode functionName = (IdentifierNode) functionNode
							.child(0);

					if (functionName.name().equals(MAIN)) {
						// CompoundStatementNode body=functionNode.getBody();
						//
						// body.remove();
						items.add(functionNode.getBody().copy());
						// callMain = this.callMain(functionNode);

					} else
						items.add((BlockItemNode) child);
				} else
					items.add((BlockItemNode) child);
			}
		}
		// assert callMain != null;
		// items.add(callMain);
		items.add(commDestroy);
		mpiProcessBody = nodeFactory.newCompoundStatementNode(this.newSource(
				"function body of " + MPI_PROCESS, CParser.COMPOUND_STATEMENT),
				items);
		formals = nodeFactory.newSequenceNode(this.newSource(
				"formal parameters of function " + MPI_PROCESS,
				CParser.DECLARATION_LIST), "FormalParameterDeclarations",
				Arrays.asList(this.variableDeclaration(MPI_RANK,
						this.basicType(BasicTypeKind.INT))));
		mpiProcessType = nodeFactory
				.newFunctionTypeNode(this.newSource("type of function "
						+ MPI_PROCESS, CParser.TYPE), this.voidType(), formals,
						true);
		mpiProcess = nodeFactory.newFunctionDefinitionNode(this.newSource(
				"definition of function", CParser.FUNCTION_DEFINITION), this
				.identifier(MPI_PROCESS), mpiProcessType, null, mpiProcessBody);
		return new Triple<>(mpiProcess, includedNodes, vars);
	}

	StatementNode callMain(FunctionDefinitionNode function) {
		for (BlockItemNode child : function.getBody()) {
			if (child == null)
				continue;
			if (child instanceof ExpressionStatementNode) {
				ExpressionNode expr = ((ExpressionStatementNode) child)
						.getExpression();

				if (expr instanceof FunctionCallNode) {
					ExpressionNode functionNode = ((FunctionCallNode) expr)
							.getFunction();

					if (functionNode instanceof IdentifierExpressionNode) {
						if (((IdentifierExpressionNode) functionNode)
								.getIdentifier().name().equals(GEN_MAIN))
							return (StatementNode) (child.copy());
					}
				}
			}
		}
		return null;
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
		TypeNode typeNode = this.basicType(type);

		return this.variableDeclaration(name, typeNode);
	}

	/**
	 * Creates the declaration node for the input variable <code>NPROCS</code>.
	 * 
	 * @return The declaration node of the input variable <code>NPROCS</code>.
	 */
	private VariableDeclarationNode nprocsDeclaration() {
		TypeNode nprocsType = this.basicType(BasicTypeKind.INT);

		nprocsType.setInputQualified(true);
		return this.variableDeclaration(NPROCS, nprocsType);
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
			SequenceNode<ExpressionNode> emptyArgNode = nodeFactory
					.newSequenceNode(
							newSource(
									"empty parameter list of " + MPI_INIT_NEW,
									CParser.ARGUMENT_LIST),
							"EmptyParameterList",
							new LinkedList<ExpressionNode>());

			if (functionName.equals(MPI_INIT)) {
				functionExpression.getIdentifier().setName(MPI_INIT_NEW);
				functionCall.setArguments(emptyArgNode);
			} else if (functionName.equals(MPI_FINALIZE)) {
				functionExpression.getIdentifier().setName(MPI_FINALIZE_NEW);
				functionCall.setArguments(emptyArgNode);
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
	private ExpressionStatementNode nprocsAssumption() throws SyntaxException {
		return this.boundAssumption(NPROCS_LOWER_BOUND, NPROCS,
				NPROCS_UPPER_BOUND);
	}

	private VariableDeclarationNode getVariabledeclaration(ASTNode root,
			String name) {
		for (ASTNode node : root.children()) {
			if (node != null
					&& node.nodeKind() == NodeKind.VARIABLE_DECLARATION) {
				VariableDeclarationNode varNode = (VariableDeclarationNode) node;

				if (varNode.getName().equals(name)) {
					return varNode;
				}
			}
		}
		return null;
	}

	/**
	 * transforms exit(k); to CMPI_destroy(MPI_COMM_WORLD); exit(k);
	 * 
	 * @param node
	 */
	private void transformExit(ASTNode node) {
		if (node instanceof ExpressionStatementNode) {
			ExpressionNode expr = ((ExpressionStatementNode) node)
					.getExpression();

			if (expr instanceof FunctionCallNode) {
				ExpressionNode function = ((FunctionCallNode) expr)
						.getFunction();

				if (function instanceof IdentifierExpressionNode) {
					String funcName = ((IdentifierExpressionNode) function)
							.getIdentifier().name();

					if (funcName.equals(EXIT)) {
						BlockItemNode commDestroy = this.commDestroy(
								COMM_DESTROY, COMM_WORLD);
						int nodeIndex = node.childIndex();
						ASTNode parent = node.parent();
						List<BlockItemNode> newItems = new LinkedList<>();

						node.remove();
						newItems.add(commDestroy);
						newItems.add((BlockItemNode) node);
						parent.setChild(
								nodeIndex,
								nodeFactory.newCompoundStatementNode(
										node.getSource(), newItems));
					}
				}
			}
		} else
			for (ASTNode child : node.children()) {
				if (child != null)
					transformExit(child);
			}
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
	@Override
	public AST transform(AST ast) throws SyntaxException {
		SequenceNode<BlockItemNode> root = ast.getRootNode();
		AST newAst;
		FunctionDefinitionNode mpiProcess, mainFunction;
		VariableDeclarationNode gcommWorld;
		List<BlockItemNode> externalList;
		SequenceNode<BlockItemNode> newRootNode;
		List<BlockItemNode> includedNodes = new ArrayList<>();
		List<VariableDeclarationNode> mainParameters = new ArrayList<>();
		int count;
		StatementNode nprocsAssumption = null;
		Triple<FunctionDefinitionNode, List<BlockItemNode>, List<VariableDeclarationNode>> result;
		VariableDeclarationNode nprocsVar = this.getVariabledeclaration(root,
				NPROCS);
		VariableDeclarationNode nprocsUpperBoundVar = this
				.getVariabledeclaration(root, NPROCS_UPPER_BOUND);
		VariableDeclarationNode nprocsLowerBoundVar = this
				.getVariabledeclaration(root, NPROCS_LOWER_BOUND);

		assert this.astFactory == ast.getASTFactory();
		assert this.nodeFactory == astFactory.getNodeFactory();
		ast.release();
		if (!this.has_gen_mainFunction(root)) {
			transformMainFunction(root);
			createNewMainFunction(root);
		}
		// change MPI_Init(...) to _MPI_Init();
		preprocessASTNode(root);
		transformExit(root);
		if (nprocsVar == null) {
			// declaring $input int NPROCS;
			nprocsVar = this.nprocsDeclaration();
			if (nprocsUpperBoundVar == null) {
				// declaring $input int NPROCS_UPPER_BOUND;
				nprocsUpperBoundVar = this.basicTypeVariableDeclaration(
						BasicTypeKind.INT, NPROCS_UPPER_BOUND);
				nprocsUpperBoundVar.getTypeNode().setInputQualified(true);
			} else {
				nprocsUpperBoundVar.parent().removeChild(
						nprocsUpperBoundVar.childIndex());
			}
			if (nprocsLowerBoundVar == null) {
				Source lowerBoundSource = this.newSource(
						"constant integer: one", CParser.INT);
				Source intTypeSource = this.newSource("int", CParser.TYPE);

				// declaring $input int NPROCS_LOWER_BOUND;
				nprocsLowerBoundVar = this.variableDeclaration(
						NPROCS_LOWER_BOUND, nodeFactory.newBasicTypeNode(
								intTypeSource, BasicTypeKind.INT),
						this.nodeFactory.newIntegerConstantNode(
								lowerBoundSource, "1"));
				nprocsLowerBoundVar.getTypeNode().setInputQualified(true);
			} else {
				nprocsLowerBoundVar.parent().removeChild(
						nprocsLowerBoundVar.childIndex());
			}
			// assuming NPROCS_LOWER_BOUND < NPROCS && NPROCS <=
			// NPROCS_UPPER_BOUND
			nprocsAssumption = this.nprocsAssumption();
		} else {
			nprocsVar.parent().removeChild(nprocsVar.childIndex());
		}
		// declaring $gcomm GCOMM_WORLD = $gcomm_create($here, NPROCS);
		gcommWorld = this.gcommDeclaration();
		result = this.mpiProcess(root);
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
		externalList.add(this.gcommsSeqDeclaration());
		externalList.add(this.gcommsSeqInitCalling());
		externalList.add(mpiProcess);
		externalList.add(mainFunction);
		newRootNode = nodeFactory.newSequenceNode(null, "TranslationUnit",
				externalList);
		this.completeSources(newRootNode);
		newAst = astFactory.newAST(newRootNode, ast.getSourceFiles());
		// newAst.prettyPrint(System.out, true);
		return newAst;
	}

	/**
	 * Create a variable declaration node of "__MPI_Sys_status__" type which
	 * should be in every process representing the status of the process which
	 * is controlled by MPI_Init() and MPI_Finalize()
	 * 
	 * @return
	 */
	private VariableDeclarationNode mpiSysStatusDeclaration() {
		TypeNode sysStatusType;
		VariableDeclarationNode node;

		sysStatusType = nodeFactory.newTypedefNameNode(nodeFactory
				.newIdentifierNode(
						newSource("MPI_Sys_status in _MPI_Process",
								CParser.IDENTIFIER), MPI_SYS_STATUS_TYPENAME),
				null);
		node = variableDeclaration(MPI_SYS_STATUS, sysStatusType,
				nodeFactory.newEnumerationConstantNode(nodeFactory
						.newIdentifierNode(
								newSource("__UNINIT",
										CParser.ENUMERATION_CONSTANT),
								"__UNINIT")));
		return node;
	}

	/**
	 * An inserted assertion "assert _my_status == __UNINIT" which is used to
	 * prevent being pruned by Pruner.
	 * 
	 * @return
	 */
	private ExpressionStatementNode mpiStatusDePruneAssertion() {
		List<ExpressionNode> assertionNodesList = new LinkedList<>();
		Source assertSrc = newSource("_my_status initial value assertion",
				CParser.EXPRESSION_STATEMENT);
		Source myStatusSrc = newSource("_my_status", CParser.IDENTIFIER);

		assertionNodesList.add(nodeFactory.newIdentifierExpressionNode(
				myStatusSrc,
				nodeFactory.newIdentifierNode(myStatusSrc, MPI_SYS_STATUS)));
		assertionNodesList.add(nodeFactory
				.newEnumerationConstantNode(nodeFactory.newIdentifierNode(
						newSource("__UNINIT", CParser.ENUMERATION_CONSTANT),
						"__UNINIT")));
		return nodeFactory.newExpressionStatementNode(this.functionCall(
				assertSrc, ASSERT, Arrays.asList((ExpressionNode) nodeFactory
						.newOperatorNode(assertSrc, Operator.EQUALS,
								assertionNodesList))));
	}
}
