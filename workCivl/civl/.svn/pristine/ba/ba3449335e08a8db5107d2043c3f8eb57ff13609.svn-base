package edu.udel.cis.vsl.civl.transform.common;

import java.util.ArrayList;
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
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IntegerConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.AssumeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CompoundStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ExpressionStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ForLoopInitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ForLoopNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.FunctionTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.transform.IF.BaseTransformer;

/**
 * MPITransformer transforms an AST of an MPI program into an AST of an
 * equivalent CIVL-C program. See {@linkplain #transform(AST)}.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class MPI2CIVLTransformer extends BaseTransformer {

	/* **************************** Static Fields ************************** */
	/**
	 * The code (short name) of this transformer.
	 */
	public static String CODE = "mpi";

	/**
	 * The long name of the transformer.
	 */
	public static String LONG_NAME = "MPITransformer";

	/**
	 * The description of this transformer.
	 */
	public static String SHORT_DESCRIPTION = "transforms C/MPI program to CIVL-C";

	/**
	 * The name of the identifier of the $comm variable in the final CIVL
	 * program.
	 */
	private static String COMM_WORLD = "MPI_COMM_WORLD";

	/**
	 * The name of the identifier of the $gcomm variable in the final CIVL
	 * program.
	 */
	private static String GCOMM_WORLD = "GCOMM_WORLD";

	/**
	 * The name of $gcomm type in the final CIVL-C program.
	 */
	private static String GCOMM_TYPE = "$gcomm";

	/**
	 * The name of MPI_Comm type in both the orginal program and the final
	 * CIVL-C program.
	 */
	private static String COMM_TYPE = "MPI_Comm";

	/**
	 * The name of the function to create a new $gcomm object in the final
	 * CIVL-C program.
	 */
	private static String GCOMM_CREATE = "$gcomm_create";

	/**
	 * The name of the function to create a new $comm object in the final CIVL-C
	 * program.
	 */
	private static String COMM_CREATE = "$comm_create";

	/**
	 * The name of the function to free a $gcomm object in the final CIVL-C
	 * program.
	 */
	private static String GCOMM_DESTROY = "$gcomm_destroy";

	/**
	 * The name of the function to free a $comm object in the final CIVL-C
	 * program.
	 */
	private static String COMM_DESTROY = "$comm_destroy";

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
	 * The name of the MPI procedure in the final CIVL-C program.
	 */
	private static String MPI_PROCESS = "MPI_Process";

	/**
	 * The name of the input variable denoting the number of MPI processes in
	 * the final CIVL-C program.
	 */
	private static String NPROCS = "__NPROCS";

	/**
	 * The name of the input variable denoting the bound of the number of MPI
	 * processes in the final CIVL-C program.
	 */
	private static String NPROCS_BOUND = "__NPROCS_BOUND";

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
	public MPI2CIVLTransformer(ASTFactory astFactory) {
		super(CODE, LONG_NAME, SHORT_DESCRIPTION, astFactory);
	}

	/* *************************** Private Methods ************************* */

	/**
	 * Creates a bound assumption in the form of:
	 * <code>$assume 0 < variable && variable <= upperBound</code>, where 0 is
	 * an implicit lower bound.
	 * 
	 * @param variable
	 *            The variable of the bound.
	 * @param upperBound
	 *            The upper bound of the variable.
	 * @return The node representing of the assumption on the bound of the
	 *         variable.
	 * @throws SyntaxException
	 */
	private AssumeNode boundAssumption(String variable, String upperBound)
			throws SyntaxException {
		IdentifierExpressionNode variableExpression = nodeFactory
				.newIdentifierExpressionNode(source,
						nodeFactory.newIdentifierNode(source, variable));
		IdentifierExpressionNode upperBoundExpression = nodeFactory
				.newIdentifierExpressionNode(source,
						nodeFactory.newIdentifierNode(source, upperBound));
		IntegerConstantNode zero = nodeFactory.newIntegerConstantNode(source,
				"0");
		List<ExpressionNode> arguments = new ArrayList<>(2);
		ExpressionNode lowerPart, upperPart;

		arguments.add(zero);
		arguments.add(variableExpression);
		lowerPart = nodeFactory.newOperatorNode(source, Operator.LT, arguments);
		arguments = new ArrayList<>(2);
		variableExpression = nodeFactory.newIdentifierExpressionNode(source,
				nodeFactory.newIdentifierNode(source, variable));
		arguments.add(variableExpression);
		arguments.add(upperBoundExpression);
		upperPart = nodeFactory
				.newOperatorNode(source, Operator.LTE, arguments);
		arguments = new ArrayList<>(2);
		arguments.add(lowerPart);
		arguments.add(upperPart);
		return nodeFactory.newAssumeNode(source,
				nodeFactory.newOperatorNode(source, Operator.LAND, arguments));
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
		commCreateArgs.add(nodeFactory.newIdentifierExpressionNode(source,
				nodeFactory.newIdentifierNode(source, GCOMM_WORLD)));
		commCreateArgs.add(nodeFactory.newIdentifierExpressionNode(source,
				nodeFactory.newIdentifierNode(source, MPI_RANK)));
		commCreate = nodeFactory.newFunctionCallNode(
				source,
				nodeFactory.newIdentifierExpressionNode(source,
						nodeFactory.newIdentifierNode(source, COMM_CREATE)),
				commCreateArgs, null);
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
		IdentifierExpressionNode function = nodeFactory
				.newIdentifierExpressionNode(source,
						nodeFactory.newIdentifierNode(source, destroy));
		List<ExpressionNode> arguments = new ArrayList<>(1);

		arguments.add(nodeFactory.newIdentifierExpressionNode(source,
				nodeFactory.newIdentifierNode(source, commName)));
		return nodeFactory.newExpressionStatementNode(nodeFactory
				.newFunctionCallNode(source, function, arguments, null));
	}

	/**
	 * Creates the declaration node for the variable <code>GCOMM_WORLD</code> ,
	 * which is of <code>$gcomm</code> type and has an initializer to call
	 * <code>$gcomm_create()</code>. That is:
	 * <code>$gcomm MPI_COMM_WORLD = $gcomm_create($here, NPROCS)</code> .
	 * 
	 * @return The declaration node of the variable <code>GCOMM_WORLD</code>.
	 */
	private VariableDeclarationNode gcommDeclaration() {
		TypeNode gcommType;
		List<ExpressionNode> gcommCreateArgs;
		ExpressionNode gcommCreate;

		gcommType = nodeFactory.newTypedefNameNode(
				nodeFactory.newIdentifierNode(source, GCOMM_TYPE), null);
		gcommCreateArgs = new ArrayList<>(2);
		gcommCreateArgs.add(nodeFactory.newHereNode(source));
		gcommCreateArgs.add(nodeFactory.newIdentifierExpressionNode(source,
				nodeFactory.newIdentifierNode(source, NPROCS)));
		gcommCreate = nodeFactory.newFunctionCallNode(
				source,
				nodeFactory.newIdentifierExpressionNode(source,
						nodeFactory.newIdentifierNode(source, GCOMM_CREATE)),
				gcommCreateArgs, null);
		return nodeFactory.newVariableDeclarationNode(source,
				nodeFactory.newIdentifierNode(source, GCOMM_WORLD), gcommType,
				gcommCreate);
	}

	/**
	 * Creates the main function for the final program, which is: <br>
	 * <code>void main(){</code><br>
	 * <code>&nbsp;&nbsp;$proc procs[NPROCS];</code><br>
	 * <code>&nbsp;&nbsp;for(int i = 0; i < NPROCS; i++){</code><br>
	 * <code>&nbsp;&nbsp;&nbsp;&nbsp;procs[i] = $spawn MPI_Process(i);</code><br>
	 * <code>&nbsp;&nbsp;}</code><br>
	 * <code>&nbsp;&nbsp;for(int i = 0; i < NPROCS; i++){</code><br>
	 * <code>&nbsp;&nbsp;&nbsp;&nbsp;$wait(procs[i]);</code><br>
	 * <code>&nbsp;&nbsp;}</code><br>
	 * <code>&nbsp;&nbsp;$gcomm_destroy(GCOMM_WORLD);</code><br>
	 * <code>}</code><br>
	 * 
	 * @return The function definition node representing the main function of
	 *         the final program.
	 * @throws SyntaxException
	 */
	private FunctionDefinitionNode mainFunction() throws SyntaxException {
		List<BlockItemNode> items = new LinkedList<BlockItemNode>();
		TypeNode procsType;
		VariableDeclarationNode procsVar;
		List<VariableDeclarationNode> initialList;
		ForLoopInitializerNode initializerNode;
		List<ExpressionNode> operatorArgs;
		ExpressionNode loopCondition, incrementer, spawnProc, waitProc, leftHandSide;
		List<ExpressionNode> callArgs;
		StatementNode assign;
		ForLoopNode forLoop;
		CompoundStatementNode mainBody;
		LinkedList<VariableDeclarationNode> newFormalList;
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
						nodeFactory.newIdentifierExpressionNode(source,
								nodeFactory.newIdentifierNode(source, NPROCS)));
		procsVar = nodeFactory.newVariableDeclarationNode(source,
				nodeFactory.newIdentifierNode(source, PROCS), procsType);
		items.add(procsVar);
		// first for loop;
		initialList = new LinkedList<>();
		initialList.add(nodeFactory.newVariableDeclarationNode(source,
				nodeFactory.newIdentifierNode(source, "i"),
				nodeFactory.newBasicTypeNode(source, BasicTypeKind.INT),
				nodeFactory.newIntegerConstantNode(source, "0")));
		initializerNode = nodeFactory.newForLoopInitializerNode(source,
				initialList);
		operatorArgs = new LinkedList<>();
		operatorArgs.add(nodeFactory.newIdentifierExpressionNode(source,
				nodeFactory.newIdentifierNode(source, "i")));
		operatorArgs.add(nodeFactory.newIdentifierExpressionNode(source,
				nodeFactory.newIdentifierNode(source, NPROCS)));

		loopCondition = nodeFactory.newOperatorNode(source, Operator.LT,
				operatorArgs);
		operatorArgs = new LinkedList<>();
		operatorArgs.add(nodeFactory.newIdentifierExpressionNode(source,
				nodeFactory.newIdentifierNode(source, "i")));

		incrementer = nodeFactory.newOperatorNode(source,
				Operator.POSTINCREMENT, operatorArgs);
		callArgs = new ArrayList<>(1);
		callArgs.add(nodeFactory.newIdentifierExpressionNode(source,
				nodeFactory.newIdentifierNode(source, "i")));
		spawnProc = nodeFactory.newSpawnNode(source, nodeFactory
				.newFunctionCallNode(source, nodeFactory
						.newIdentifierExpressionNode(source, nodeFactory
								.newIdentifierNode(source, MPI_PROCESS)),
						callArgs, null));
		operatorArgs = new LinkedList<>();
		operatorArgs.add(nodeFactory.newIdentifierExpressionNode(source,
				nodeFactory.newIdentifierNode(source, PROCS)));
		operatorArgs.add(nodeFactory.newIdentifierExpressionNode(source,
				nodeFactory.newIdentifierNode(source, "i")));
		leftHandSide = nodeFactory.newOperatorNode(source, Operator.SUBSCRIPT,
				operatorArgs);
		operatorArgs = new LinkedList<>();
		operatorArgs.add(leftHandSide);
		operatorArgs.add(spawnProc);
		assign = nodeFactory.newExpressionStatementNode(nodeFactory
				.newOperatorNode(source, Operator.ASSIGN, operatorArgs));
		forLoop = nodeFactory.newForLoopNode(source, initializerNode,
				loopCondition, incrementer, assign, null);
		items.add(forLoop);

		// second for loop;
		initialList = new LinkedList<>();
		initialList.add(nodeFactory.newVariableDeclarationNode(source,
				nodeFactory.newIdentifierNode(source, "i"),
				nodeFactory.newBasicTypeNode(source, BasicTypeKind.INT),
				nodeFactory.newIntegerConstantNode(source, "0")));
		initializerNode = nodeFactory.newForLoopInitializerNode(source,
				initialList);
		operatorArgs = new LinkedList<>();
		operatorArgs.add(nodeFactory.newIdentifierExpressionNode(source,
				nodeFactory.newIdentifierNode(source, "i")));
		operatorArgs.add(nodeFactory.newIdentifierExpressionNode(source,
				nodeFactory.newIdentifierNode(source, NPROCS)));

		loopCondition = nodeFactory.newOperatorNode(source, Operator.LT,
				operatorArgs);
		operatorArgs = new LinkedList<>();
		operatorArgs.add(nodeFactory.newIdentifierExpressionNode(source,
				nodeFactory.newIdentifierNode(source, "i")));

		incrementer = nodeFactory.newOperatorNode(source,
				Operator.POSTINCREMENT, operatorArgs);
		callArgs = new ArrayList<>(1);

		operatorArgs = new LinkedList<>();
		operatorArgs.add(nodeFactory.newIdentifierExpressionNode(source,
				nodeFactory.newIdentifierNode(source, PROCS)));
		operatorArgs.add(nodeFactory.newIdentifierExpressionNode(source,
				nodeFactory.newIdentifierNode(source, "i")));
		callArgs.add(nodeFactory.newOperatorNode(source, Operator.SUBSCRIPT,
				operatorArgs));
		waitProc = nodeFactory.newFunctionCallNode(
				source,
				nodeFactory.newIdentifierExpressionNode(source,
						nodeFactory.newIdentifierNode(source, WAIT)), callArgs,
				null);
		forLoop = nodeFactory.newForLoopNode(source, initializerNode,
				loopCondition, incrementer,
				nodeFactory.newExpressionStatementNode(waitProc), null);
		items.add(forLoop);

		// destroying GCOMM_WROLD;
		items.add(gcommDestroy);

		// constructing the function definition node.
		mainBody = nodeFactory.newCompoundStatementNode(source, items);
		newFormalList = new LinkedList<>();
		newFormalList.add(nodeFactory.newVariableDeclarationNode(source,
				nodeFactory.newIdentifierNode(source, MPI_RANK),
				nodeFactory.newBasicTypeNode(source, BasicTypeKind.INT)));
		formals = nodeFactory.newSequenceNode(source,
				"FormalParameterDeclarations", newFormalList);
		mainType = nodeFactory.newFunctionTypeNode(source,
				nodeFactory.newVoidTypeNode(source), formals, true);
		mainFunction = nodeFactory.newFunctionDefinitionNode(source,
				nodeFactory.newIdentifierNode(source, "main"), mainType, null,
				mainBody);
		return mainFunction;
	}

	/**
	 * Constructs the function MPI_Process() from the original MPI program. It
	 * is a wrapper of the original MPI program with some additional features: <br>
	 * <code>void MPI_Process(){</code><br>
	 * <code>&nbsp;&nbsp;$comm MPI_COMM_WORLD = $comm_create(...);</code><br>
	 * <code>&nbsp;&nbsp;//SLIGHTLY-MODIFIED ORIGINAL PROGRAM;</code><br>
	 * <code>&nbsp;&nbsp;int a, b, ...;</code><br>
	 * <code>&nbsp;&nbsp;... function(){...}</code><br>
	 * <code>&nbsp;&nbsp;...</code><br>
	 * <code>&nbsp;&nbsp;... __main(){...} // renamed main() to __main()</code><br>
	 * <code>&nbsp;&nbsp;....</code><br>
	 * <code>&nbsp;&nbsp;//ORIGINAL PROGRAM ENDS HERE;</code><br>
	 * <code>&nbsp;&nbsp;__main();</code><br>
	 * <code>&nbsp;&nbsp;$comm_destroy(MPI_COMM_WORLD);</code><br>
	 * <code>}</code>
	 * 
	 * @param root
	 *            The root node of the AST of the original MPI program.
	 * @param includedNodes
	 *            The set of AST nodes that are parsed from header files. These
	 *            nodes will be moved up to the higher scope (i.e., the file
	 *            scope of the final AST). When invoking this function, this
	 *            parameter should be an empty list and this function will
	 *            update this list.
	 * @param vars
	 *            The list of variable declaration nodes that are the arguments
	 *            of the original main function. These variables will be moved
	 *            up to the higher scope (i.e., the file scope of the final AST)
	 *            and become $input variables of the final AST. When invoking
	 *            this function, this parameter should be an empty list and this
	 *            function will update this list.
	 * @return The function definition node of MPI_Process.
	 */
	private FunctionDefinitionNode mpiProcess(SequenceNode<ASTNode> root,
			List<ASTNode> includedNodes, List<VariableDeclarationNode> vars) {
		List<BlockItemNode> items;
		int number;
		ExpressionStatementNode callMain;
		CompoundStatementNode mpiProcessBody;
		List<VariableDeclarationNode> newFormalList;
		SequenceNode<VariableDeclarationNode> formals;
		FunctionTypeNode mpiProcessType;
		FunctionDefinitionNode mpiProcess;
		VariableDeclarationNode commVar = this.commDeclaration();
		ExpressionStatementNode commDestroy = this.commDestroy(COMM_DESTROY,
				COMM_WORLD);

		callMain = nodeFactory.newExpressionStatementNode(nodeFactory
				.newFunctionCallNode(source,
						nodeFactory
								.newIdentifierExpressionNode(source,
										nodeFactory.newIdentifierNode(source,
												MPI_MAIN)),
						new ArrayList<ExpressionNode>(), null));

		// build MPI_Process() function:
		items = new LinkedList<>();
		number = root.numChildren();
		items.add(commVar);
		for (int i = 0; i < number; i++) {
			ASTNode child = root.child(i);
			String sourceFile = child.getSource().getFirstToken()
					.getSourceFile().getName();

			root.removeChild(i);
			if (sourceFile.equals("stdio.cvl")) {
				includedNodes.add(child);
			} else if (sourceFile.endsWith(".h")) {
				if (child.nodeKind() == NodeKind.VARIABLE_DECLARATION) {
					VariableDeclarationNode variableDeclaration = (VariableDeclarationNode) child;

					if (sourceFile.equals("stdio.h")) {
						// keep variable declaration nodes from stdio, i.e.,
						// stdout, stdin, etc.
						items.add(variableDeclaration);
					} else if (!variableDeclaration.getName()
							.equals(COMM_WORLD)) {
						// ignore the MPI_COMM_WORLD declaration in mpi.h.
						includedNodes.add(child);
					}
				} else {
					includedNodes.add(child);
				}
			} else {
				if (child.nodeKind() == NodeKind.VARIABLE_DECLARATION) {
					VariableDeclarationNode variable = (VariableDeclarationNode) child;

					if (variable.getTypeNode().isInputQualified()) {
						vars.add(variable);
						continue;
					}
				}
				if (child.nodeKind() == NodeKind.FUNCTION_DEFINITION) {
					FunctionDefinitionNode functionNode = (FunctionDefinitionNode) child;
					IdentifierNode functionName = (IdentifierNode) functionNode
							.child(0);

					if (functionName.name().equals("main")) {
						functionName.setName(MPI_MAIN);
						processMainFunction(functionNode, vars);
					}
				}
				items.add((BlockItemNode) child);
			}
		}
		items.add(callMain);
		items.add(commDestroy);
		mpiProcessBody = nodeFactory.newCompoundStatementNode(root.getSource(),
				items);
		newFormalList = new LinkedList<>();
		newFormalList.add(nodeFactory.newVariableDeclarationNode(source,
				nodeFactory.newIdentifierNode(source, MPI_RANK),
				nodeFactory.newBasicTypeNode(source, BasicTypeKind.INT)));
		formals = nodeFactory.newSequenceNode(source,
				"FormalParameterDeclarations", newFormalList);
		mpiProcessType = nodeFactory.newFunctionTypeNode(source,
				nodeFactory.newVoidTypeNode(source), formals, true);
		mpiProcess = nodeFactory.newFunctionDefinitionNode(source,
				nodeFactory.newIdentifierNode(source, MPI_PROCESS),
				mpiProcessType, null, mpiProcessBody);
		return mpiProcess;
	}

	/**
	 * Creates the declaration node for the input variable <code>NPROCS</code>.
	 * 
	 * @return The declaration node of the input variable <code>NPROCS</code>.
	 */
	private VariableDeclarationNode nprocsBoundDeclaration() {
		TypeNode nprocsBoundType = nodeFactory.newBasicTypeNode(source,
				BasicTypeKind.INT);

		nprocsBoundType.setInputQualified(true);
		return nodeFactory.newVariableDeclarationNode(source,
				nodeFactory.newIdentifierNode(source, NPROCS_BOUND),
				nprocsBoundType);
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
	 * Translates an <code>MPI_Init(...)</code> function call into
	 * <code>__MPI_Init()</code>.
	 * 
	 * @param functionCall
	 */
	private void preprocessFunctionCall(FunctionCallNode functionCall) {
		if (functionCall.getFunction().expressionKind() == ExpressionKind.IDENTIFIER_EXPRESSION) {
			IdentifierExpressionNode functionExpression = (IdentifierExpressionNode) functionCall
					.getFunction();

			if (functionExpression.getIdentifier().name().equals(MPI_INIT)) {
				List<ExpressionNode> arguments = new ArrayList<>(0);

				functionExpression.getIdentifier().setName(MPI_INIT_NEW);
				functionCall.setChild(1, nodeFactory.newSequenceNode(source,
						"ActualParameterList", arguments));
			}
		}
	}

	/**
	 * Processes the original main function, including:
	 * <ul>
	 * <li>Removes all arguments of the function;</li>
	 * </ul>
	 * 
	 * @param mainFunction
	 *            The function definition node representing the original main
	 *            function.
	 * @param vars
	 *            The list of variable declaration nodes that are the arguments
	 *            of the original main function. These variables will be moved
	 *            up to the higher scope (i.e., the file scope of the final AST)
	 *            and become $input variables of the final AST. When invoking
	 *            this function, this parameter should be an empty list and this
	 *            function will update this list.
	 */
	private void processMainFunction(FunctionDefinitionNode mainFunction,
			List<VariableDeclarationNode> inputVars) {
		FunctionTypeNode functionType = mainFunction.getTypeNode();
		SequenceNode<VariableDeclarationNode> parameters = functionType
				.getParameters();
		int count = parameters.numChildren();

		if (count > 0) {
			List<VariableDeclarationNode> newParameters = new ArrayList<>(0);

			for (int k = 0; k < count; k++) {
				VariableDeclarationNode parameter = parameters
						.getSequenceChild(k);

				parameters.removeChild(k);
				parameter.getTypeNode().setInputQualified(true);
				inputVars.add(parameter);
			}
			functionType.setParameters(nodeFactory.newSequenceNode(
					parameters.getSource(), "FormalParameterDeclarations",
					newParameters));
		}
	}

	/* ********************* Methods From BaseTransformer ****************** */

	/**
	 * Transform an AST of a pure MPI program in C into an equivalent AST of
	 * CIVL-C program.<br>
	 * Given an MPI program:<br>
	 * <code>#include &lt;mpi.h&gt;<br>
	 * ...<br>
	 * #include &lt;stdio.h&gt; <br>
	 * int a, b, ...;<br>
	 * ... function(){<br>
	 * &nbsp;&nbsp;...<br>
	 * }<br>
	 * ...<br>
	 * int main(){<br>
	 * &nbsp;&nbsp;....<br>
	 * }<br></code>
	 * 
	 * It is translated to the following program:<br>
	 * <code>
	 * #include &lt; mpi.h &gt; // all included files are moved above to the new file scope.<br>
	 * ...<br>
	 * #include &lt; stdio.h &gt;<br>
	 * $input int argc;//optional, only necessary when the original main function has arguments.<br>
	 * $input char** argv;//optional, only necessary when the original main function has arguments.<br>
	 * $input int NPROCS;<br>
	 * $gcomm GCOMM_WORLD = $gcomm_create($here, NPROCS);<br>
	 * <br>
	 * void MPI_Process(int _rank){<br>
	 * &nbsp;&nbsp;...<br>
	 * }<br>
	 * void main(){<br>
	 * &nbsp;&nbsp;$proc procs[NPROCS];<br><br>
	 * &nbsp;&nbsp;for(int i = 0; i < NPROCS; i++)<br>
	 * &nbsp;&nbsp;&nbsp;&nbsp;procs[i] = $spawn MPI_Process(i);<br>
	 * &nbsp;&nbsp;for(int i = 0; i < NPROCS; i++)<br>
	 * &nbsp;&nbsp;&nbsp;&nbsp;$wait(procs[i]);<br>
	 * &nbsp;&nbsp;$gcomm_destroy(GCOMM_WORLD);<br>
	 * }</code> <br>
	 * Whereas MPI_Process() is a wrapper of the original MPI program with some
	 * special handling:<br>
	 * <code>
	 * void MPI_Process(){<br>
	 * &nbsp;&nbsp;$comm MPI_COMM_WORLD = $comm_create(...);<br><br>
	 * &nbsp;&nbsp;//SLIGHTLY-MODIFIED ORIGINAL PROGRAM;<br>
	 * &nbsp;&nbsp;int a, b, ...;<br>
	 * &nbsp;&nbsp;... function(){...}<br>
	 * &nbsp;&nbsp;...<br>
	 * &nbsp;&nbsp;... __main(){...} // renamed main() to __main()<br>
	 * &nbsp;&nbsp;....<br>
	 * &nbsp;&nbsp;//ORIGINAL PROGRAM ENDS HERE;<br>
	 * &nbsp;&nbsp;__main();<br>
	 * &nbsp;&nbsp;$comm_destroy(MPI_COMM_WORLD);<br>
	 * }<br></code>
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
		VariableDeclarationNode nprocsBoundVar;
		SequenceNode<ASTNode> newRootNode;
		List<ASTNode> includedNodes = new ArrayList<ASTNode>();
		List<VariableDeclarationNode> mainParameters = new ArrayList<>();
		int count;
		AssumeNode nprocsAssumption;

		this.source = root.getSource();// TODO needs a good source
		assert this.astFactory == ast.getASTFactory();
		assert this.nodeFactory == astFactory.getNodeFactory();
		ast.release();
		// change MPI_Init(...) to _MPI_Init();
		preprocessASTNode(root);
		// declaring $input int NPROCS;
		nprocsVar = this.nprocsDeclaration();
		// declaring $input int NPROCS_BOUND;
		nprocsBoundVar = this.nprocsBoundDeclaration();
		// assuming 0 < NPROCS && NPROCS <= NPROCS_BOUND
		nprocsAssumption = this.boundAssumption(NPROCS, NPROCS_BOUND);
		// declaring $gcomm GCOMM_WORLD = $gcomm_create($here, NPROCS);
		gcommWorld = this.gcommDeclaration();
		// defining MPI_Process(_rank){...};
		mpiProcess = this.mpiProcess((SequenceNode<ASTNode>) root,
				includedNodes, mainParameters);
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
		externalList.add(nprocsBoundVar);
		externalList.add(nprocsAssumption);
		externalList.add(gcommWorld);
		externalList.add(mpiProcess);
		externalList.add(mainFunction);
		newRootNode = nodeFactory.newSequenceNode(null, "TranslationUnit",
				externalList);
		newAst = astFactory.newTranslationUnit(newRootNode);
		return newAst;
	}
}
