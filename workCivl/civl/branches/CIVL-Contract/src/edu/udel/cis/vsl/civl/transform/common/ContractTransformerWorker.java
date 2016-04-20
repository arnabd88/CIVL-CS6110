package edu.udel.cis.vsl.civl.transform.common;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.entity.IF.Function;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode.NodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CompoundStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.FunctionTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.ast.type.IF.FunctionType;
import edu.udel.cis.vsl.abc.ast.type.IF.ObjectType;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.front.IF.CivlcTokenConstant;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.civl.transform.IF.ContractTransformer;

/**
 * This transformer serves for CIVL Contracts mode.
 * 
 * @author ziqingluo
 *
 */
public class ContractTransformerWorker extends BaseWorker {

	private final static String CONTRACT_PREFIX = "_contract_";

	private final static String CONTRACT_VAR_NAME = "_gen";

	private final static String HAVOC_ID = "$havoc";

	public ContractTransformerWorker(ASTFactory astFactory) {
		super(ContractTransformer.LONG_NAME, astFactory);
		identifierPrefix = CONTRACT_PREFIX;
	}

	@Override
	public AST transform(AST ast) throws SyntaxException {
		SequenceNode<BlockItemNode> root = ast.getRootNode();
		String sourceFileName;
		List<FunctionDefinitionNode> funcDefInSrc = new LinkedList<>();
		List<BlockItemNode> externalList = new LinkedList<>();
		SequenceNode<BlockItemNode> newRootNode;
		FunctionDeclarationNode havocDecl;
		AST newAst;
		int count;

		ast.release();
		transformMainFunction(root);
		havocDecl = createHavocFunctionDeclaration();
		havocDecl.setSystemFunctionSpeciier(true);
		externalList.add(havocDecl);
		for (ASTNode child : root) {
			// TODO: some transformers happened previously make some child null
			// ?
			// TODO: get rid of null source !!!!
			if (child == null || child.getSource() == null)
				continue;
			sourceFileName = child.getSource().getFirstToken().getSourceFile()
					.getName();
			if (!sourceFileName.endsWith(".cvl")
					&& !sourceFileName.endsWith(".cvh"))
				transformWorker(child, funcDefInSrc);
		}
		count = root.numChildren();
		for (int i = 0; i < count; i++) {
			BlockItemNode child = root.getSequenceChild(i);
			root.removeChild(i);
			externalList.add(child);
		}
		externalList.add(mainFunction(funcDefInSrc));
		newRootNode = nodeFactory.newSequenceNode(null, "TranslationUnit",
				externalList);
		completeSources(newRootNode);
		newAst = astFactory.newAST(newRootNode, ast.getSourceFiles(),
				ast.isWholeProgram());
		return newAst;
	}

	private AST transformWorker(ASTNode node,
			List<FunctionDefinitionNode> funcDefInSrc) throws SyntaxException {

		if (node != null) {
			if (node.nodeKind().equals(NodeKind.FUNCTION_DEFINITION)) {
				funcDefInSrc.add((FunctionDefinitionNode) node);
			} else if (node.numChildren() > 0)
				for (ASTNode child : node.children())
					this.transformWorker(child, funcDefInSrc);
		}
		return null;
	}

	private FunctionDefinitionNode mainFunction(
			List<FunctionDefinitionNode> funcDefsInSrc) throws SyntaxException {
		List<BlockItemNode> items = new LinkedList<BlockItemNode>();
		List<VariableDeclarationNode> declsComponents = new LinkedList<>();
		List<StatementNode> callOrConVerifys = new LinkedList<>();
		SequenceNode<VariableDeclarationNode> formals;
		FunctionTypeNode mainType;
		FunctionDefinitionNode mainFunction;
		int varaibleNameCounter = 0;
		CompoundStatementNode mainBody;

		// constructing main function body:
		for (FunctionDefinitionNode funcDef : funcDefsInSrc) {
			Function funcDecl = funcDef.getEntity();
			FunctionType funcType = funcDecl.getType();
			int numParameters = funcType.getNumParameters();
			List<ExpressionNode> parameterIDs = new LinkedList<>();
			FunctionCallNode funcCall;

			// creating variables for parameters:
			for (int i = 0; i < numParameters; i++) {
				ObjectType parameterType = funcType.getParameterType(i);
				String varName = CONTRACT_PREFIX + CONTRACT_VAR_NAME
						+ varaibleNameCounter++;
				IdentifierNode varNameNode = nodeFactory.newIdentifierNode(
						newSource(
								"variable " + varName + " for "
										+ funcDecl.getName(),
								CivlcTokenConstant.DECLARATION), varName);
				TypeNode varTypeNode = typeNode(parameterType);
				VariableDeclarationNode varDecl;
				OperatorNode addressOfVar;
				ExpressionNode havocCall;

				parameterIDs.add(identifierExpression(varName));
				varDecl = nodeFactory.newVariableDeclarationNode(
						varNameNode.getSource(), varNameNode, varTypeNode);
				declsComponents.add(varDecl);
				// TODO: notice pointers:
				addressOfVar = nodeFactory.newOperatorNode(
						newSource("&" + varName, CivlcTokenConstant.OPERATOR),
						Operator.ADDRESSOF, identifierExpression(varName));
				// create $havoc call for it:

				havocCall = nodeFactory.newFunctionCallNode(
						newSource(HAVOC_ID + "(" + varName + ")",
								CivlcTokenConstant.CALL),
						identifierExpression(HAVOC_ID), Arrays
								.asList(addressOfVar), null);
				callOrConVerifys.add(nodeFactory
						.newExpressionStatementNode(havocCall));
			}
			// TODO: improve source here:
			// TODO: solve main function problem:
			if (!funcDecl.getName().equals("main")) {
				ExpressionNode contractVerifyNode;

				// funcCall = nodeFactory.newFunctionCallNode(
				// newSource(funcDecl.getName() + "(...)",
				// CivlcTokenConstant.CALL),
				// identifierExpression(funcDecl.getName()), parameterIDs,
				// null);
				contractVerifyNode = nodeFactory.newContractVerifyNode(
						newSource(funcDecl.getName() + "(...)",
								CivlcTokenConstant.SPAWN),
						identifierExpression(funcDecl.getName()), parameterIDs,
						null);
				callOrConVerifys.add(nodeFactory
						.newExpressionStatementNode(contractVerifyNode));
				// callOrConVerifys.add(contractVerifyNode);
			}
		}
		items.addAll(declsComponents);
		items.addAll(callOrConVerifys);
		mainBody = nodeFactory.newCompoundStatementNode(this.newSource(
				"main body", CivlcTokenConstant.COMPOUND_STATEMENT), items);
		formals = nodeFactory.newSequenceNode(this.newSource(
				"formal parameter of the declaration of the main function",
				CivlcTokenConstant.DECLARATION_LIST),
				"FormalParameterDeclarations",
				new ArrayList<VariableDeclarationNode>());
		mainType = nodeFactory.newFunctionTypeNode(this.newSource(
				"type of the main function", CivlcTokenConstant.TYPE), this
				.basicType(BasicTypeKind.INT), formals, true);
		mainFunction = nodeFactory.newFunctionDefinitionNode(this.newSource(
				"definition of the main function",
				CivlcTokenConstant.FUNCTION_DEFINITION), this
				.identifier("main"), mainType, null, mainBody);
		return mainFunction;
	}

	private FunctionDeclarationNode createHavocFunctionDeclaration() {
		IdentifierNode havocNode = nodeFactory.newIdentifierNode(
				newSource("$havoc", CivlcTokenConstant.IDENTIFIER), HAVOC_ID);
		IdentifierNode havocFormalIdNode = nodeFactory.newIdentifierNode(
				newSource("ptr", CivlcTokenConstant.IDENTIFIER), "ptr");
		VariableDeclarationNode havocFormal = nodeFactory
				.newVariableDeclarationNode(
						newSource("void *ptr", CivlcTokenConstant.DECLARATION),
						havocFormalIdNode, nodeFactory.newPointerTypeNode(
								newSource("void *", CivlcTokenConstant.TYPE),
								nodeFactory.newVoidTypeNode(newSource("void",
										CivlcTokenConstant.TYPE))));
		FunctionTypeNode funcTypeNode;

		funcTypeNode = nodeFactory.newFunctionTypeNode(
				newSource("void $havoc(void *)", CivlcTokenConstant.TYPE),
				nodeFactory.newVoidTypeNode(newSource("void",
						CivlcTokenConstant.TYPE)), nodeFactory.newSequenceNode(
						newSource("void *ptr",
								CivlcTokenConstant.PARAMETER_LIST),
						"void *ptr", Arrays.asList(havocFormal)), false);
		return nodeFactory.newFunctionDeclarationNode(
				newSource("$system void $havoc(void *ptr)",
						CivlcTokenConstant.DECLARATION), havocNode,
				funcTypeNode, null);
	}

	// private Pair<List<BlockItemNode>, List<VariableDeclarationNode>>
	// processOldProgram(
	// SequenceNode<BlockItemNode> root) {
	// int number = root.numChildren();
	// List<BlockItemNode> includedNodes = new LinkedList<>();
	// List<BlockItemNode> items = new LinkedList<>();
	// List<VariableDeclarationNode> vars = new ArrayList<>();
	//
	// for (int i = 0; i < number; i++) {
	// BlockItemNode child = root.getSequenceChild(i);
	// String sourceFile;
	//
	// if (child == null)
	// continue;
	// sourceFile = child.getSource().getFirstToken().getSourceFile()
	// .getName();
	// root.removeChild(i);
	// if (sourceFile.equals("mpi.cvl")) {
	// if (child.nodeKind() == NodeKind.VARIABLE_DECLARATION) {
	// VariableDeclarationNode variableDeclaration = (VariableDeclarationNode)
	// child;
	// includedNodes.add(child);
	// } else
	// includedNodes.add(child);
	// } else if (sourceFile.equals("pthread.cvl")) {
	// // extern void *value_ptr_value = NULL;
	// // extern $scope root = $here;
	// // pthread_t * pool[];
	//
	// if (child.nodeKind() == NodeKind.VARIABLE_DECLARATION) {
	// VariableDeclarationNode variableDeclaration = (VariableDeclarationNode)
	// child;
	// String varName = variableDeclaration.getName();
	//
	// if (varName.equals(Pthread2CIVLWorker.PTHREAD_GPOOL)
	// // || varName.equals(PTHREAD_ROOT)
	// || varName.equals(PTHREAD_PTR))
	// // keep variable declaration nodes for _pool in
	// // pthread.cvl
	// items.add(variableDeclaration);
	// else
	// includedNodes.add(child);
	// } else if (child.nodeKind() == NodeKind.FUNCTION_DEFINITION) {
	// FunctionDefinitionNode functionDef = (FunctionDefinitionNode) child;
	// String name = functionDef.getName();
	//
	// if (name.equals(Pthread2CIVLWorker.PTHREAD_EXIT_MAIN_NEW)
	// || name.equals(PTHREAD_JOIN)
	// || name.equals(Pthread2CIVLWorker.PTHREAD_CREATE)
	// || name.equals(Pthread2CIVLWorker.PTHREAD_EXIT_NEW))
	// // // ||
	// // name.equals(Pthread2CIVLWorker.PTHREAD_MUTEX_LOCK))
	// // || name.equals(PTHREAD_MUTEX_UNLOCK)
	// // || name.equals(PTHREAD_MUTEX_TRYLOCK)
	// // || name.equals(PTHREAD_COND_WAIT))
	// items.add(functionDef);
	// else
	// includedNodes.add(child);
	// } else
	// includedNodes.add(child);
	// } else if (sourceFile.equals("stdio.h")) {
	// // ignore the variable declaration in stdio.h
	// if (child.nodeKind() != NodeKind.VARIABLE_DECLARATION)
	// includedNodes.add(child);
	// } else if (sourceFile.equals("stdio.cvl")) {
	// // keep variable declaration nodes from stdio.cvl, i.e.,
	// // stdout, stdin, stderr, etc.
	// if (child.nodeKind() == NodeKind.VARIABLE_DECLARATION) {
	// VariableDeclarationNode varDecl = (VariableDeclarationNode) child;
	//
	// varDecl.setExternStorage(false);
	// items.add(varDecl);
	// } else
	// includedNodes.add(child);
	// } else if (sourceFile.equals("mpi.h")) {
	// if (child.nodeKind() == NodeKind.VARIABLE_DECLARATION) {
	// VariableDeclarationNode variableDeclaration = (VariableDeclarationNode)
	// child;
	//
	// // ignore the MPI_COMM_WORLD declaration in mpi.h.
	// if (!variableDeclaration.getName().equals(COMM_WORLD))
	// includedNodes.add(child);
	// } else
	// includedNodes.add(child);
	// } else if (CIVLConstants.getAllCLibraries().contains(sourceFile)) {//
	// sourceFile.endsWith(".h"))
	// // {
	// includedNodes.add(child);
	// } else if (sourceFile.endsWith(".cvh")
	// || sourceFile.equals("civl-cuda.cvl")
	// || sourceFile.equals("civl-mpi.cvl")
	// || sourceFile.equals("civl-omp.cvl")
	// || sourceFile.equals("civl-pthread.cvl")
	// || sourceFile.equals("civlc.cvl")
	// || sourceFile.equals("comm.cvl")
	// || sourceFile.equals("concurrency.cvl")
	// || sourceFile.equals("cuda.cvl")
	// || sourceFile.equals("math.cvl")
	// || sourceFile.equals("mpi.cvl")
	// || sourceFile.equals("omp.cvl")
	// || sourceFile.equals("pthread-functions.cvl")
	// || sourceFile.equals("pthread-types.cvl")
	// || sourceFile.equals("sched.cvl")
	// || sourceFile.equals("seq.cvl")
	// || sourceFile.equals("stdio.cvl")
	//
	// || sourceFile.equals("string.cvl")) {
	// includedNodes.add(child);
	// } else {
	// if (child.nodeKind() == NodeKind.VARIABLE_DECLARATION) {
	// VariableDeclarationNode variable = (VariableDeclarationNode) child;
	//
	// if (variable.getTypeNode().isInputQualified()
	// || variable.getTypeNode().isOutputQualified()
	// || (sourceFile.equals(GeneralTransformer.LONG_NAME) && variable
	// .getName().equals(GeneralWorker._argvName))) {
	// vars.add(variable);
	// continue;
	// }
	// }
	// if (child.nodeKind() == NodeKind.FUNCTION_DEFINITION) {
	// FunctionDefinitionNode functionNode = (FunctionDefinitionNode) child;
	// IdentifierNode functionName = (IdentifierNode) functionNode
	// .child(0);
	//
	// if (functionName.name().equals(MAIN)) {
	// // CompoundStatementNode body=functionNode.getBody();
	// //
	// // body.remove();
	// items.add(functionNode.getBody().copy());
	// // callMain = this.callMain(functionNode);
	//
	// } else
	// items.add((BlockItemNode) child);
	// } else
	// items.add((BlockItemNode) child);
	// }
	// }
	// return new Pair<>(includedNodes, vars);
	// }
}
