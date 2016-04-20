package edu.udel.cis.vsl.civl.transform.common;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.CastNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.DotNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CompoundStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ExpressionStatementNode;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;

public class Cuda2CIVLTransformer extends CIVLBaseTransformer {

	protected Cuda2CIVLTransformer(String code, String longName,
			String shortDescription, ASTFactory astFactory) {
		super(code, longName, shortDescription, astFactory);
	}

	@Override
	public AST transform(AST ast) throws SyntaxException {
		// TODO Auto-generated method stub
		return null;
	}

	// translates "cudaMalloc( (void**) ptrPtr, size)" to
	// "*ptrPtr = (type)$malloc($root, size), cudaSuccess"
	// where "type" is the type of *ptrPtr
	protected OperatorNode cudaMallocTransform(FunctionCallNode cudaMallocCall) {
		Source source = cudaMallocCall.getSource();
		// find the pointer
		ExpressionNode ptrPtr = cudaMallocCall.getArgument(0);
		while (ptrPtr instanceof CastNode) {
			ptrPtr = ((CastNode) ptrPtr).getArgument();
		}
		ExpressionNode size = cudaMallocCall.getArgument(1);
		// build lhs expression
		ExpressionNode lhs = nodeFactory.newOperatorNode(
				cudaMallocCall.getSource(), Operator.DEREFERENCE,
				Arrays.asList(ptrPtr.copy()));
		// build rhs expression
		FunctionCallNode mallocCall = nodeFactory.newFunctionCallNode(
				source,
				this.identifierExpression(source, "$malloc"),
				Arrays.asList(this.identifierExpression(source, "$root"),
						size.copy()), null);
		CastNode mallocCast = nodeFactory.newCastNode(source,
				this.typeNode(source, lhs.getType()), mallocCall);
		ExpressionNode rhs = nodeFactory.newOperatorNode(
				source,
				Operator.COMMA,
				Arrays.asList(mallocCast,
						this.identifierExpression(source, "cudaSuccess")));
		// create assign node
		OperatorNode assignment = nodeFactory.newOperatorNode(
				cudaMallocCall.getSource(), Operator.ASSIGN,
				Arrays.asList(lhs, rhs));
		return assignment;
	}

	protected FunctionDefinitionNode mainDefinitionTransform(
			FunctionDefinitionNode oldMain) {
		Source source = oldMain.getSource();
		FunctionDefinitionNode innerMainDefinition = oldMain.copy();
		innerMainDefinition.setIdentifier(nodeFactory.newIdentifierNode(source,
				"_main"));
		FunctionCallNode cudaInitCall = nodeFactory.newFunctionCallNode(source,
				this.identifierExpression(source, "_cudaInit"),
				Collections.<ExpressionNode> emptyList(), null);
		FunctionCallNode innerMainCall = nodeFactory.newFunctionCallNode(
				source, this.identifierExpression(source, "_main"),
				Collections.<ExpressionNode> emptyList(), null);
		FunctionCallNode cudaFinalizeCall = nodeFactory.newFunctionCallNode(
				source, this.identifierExpression(source, "_cudaFinalize"),
				Collections.<ExpressionNode> emptyList(), null);
		CompoundStatementNode newMainBody = nodeFactory
				.newCompoundStatementNode(
						source,
						Arrays.<BlockItemNode> asList(
								innerMainDefinition,
								nodeFactory
										.newExpressionStatementNode(cudaInitCall),
								nodeFactory
										.newExpressionStatementNode(innerMainCall),
								nodeFactory
										.newExpressionStatementNode(cudaFinalizeCall)));
		FunctionDefinitionNode newMain = nodeFactory.newFunctionDefinitionNode(
				source, nodeFactory.newIdentifierNode(source, "main"), oldMain
						.getTypeNode().copy(), null, newMainBody);
		return newMain;
	}

	private String transformKernelName(String name) {
		return "_kernel_" + name;
	}

	protected FunctionDefinitionNode kernelDefinitonTransform(
			FunctionDefinitionNode oldDefinition) {
		// TODO: add execution configuration parameters as regular parameters
		Source source = oldDefinition.getSource();
		FunctionDefinitionNode innerKernelDefinition = this
				.buildInnerKernelDefinition(oldDefinition.getBody());
		String newKernelName = this.transformKernelName(oldDefinition
				.getIdentifier().name());
		FunctionCallNode enqueueKernelCall = nodeFactory.newFunctionCallNode(
				source,
				this.identifierExpression(source, "_enqueueKernel"),
				Arrays.asList(this.identifierExpression(source, "s"),
						this.identifierExpression(source, "_kernel")), null);
		CompoundStatementNode newKernelBody = nodeFactory
				.newCompoundStatementNode(source, Arrays.asList(
						innerKernelDefinition, nodeFactory
								.newExpressionStatementNode(enqueueKernelCall)));
		FunctionDefinitionNode newKernel = nodeFactory
				.newFunctionDefinitionNode(source,
						nodeFactory.newIdentifierNode(source, newKernelName),
						oldDefinition.getTypeNode(), null, newKernelBody);
		return newKernel;
	}

	protected List<BlockItemNode> extractSharedVariableDeclarations(
			CompoundStatementNode statements) {
		List<BlockItemNode> declarations = new ArrayList<BlockItemNode>();
		for (@SuppressWarnings("unused")
		BlockItemNode item : statements) {
			// TODO: if item is a VariableDeclarationNode and is qualified as a
			// shared variable, add it to declarations, and remove from
			// statements (remove())
		}
		return declarations;
	}

	protected FunctionDefinitionNode buildInnerKernelDefinition(
			CompoundStatementNode body) {
		Source source = body.getSource();
		VariableDeclarationNode thisDeclaration = nodeFactory
				.newVariableDeclarationNode(source, nodeFactory
						.newIdentifierNode(source, "this"), nodeFactory
						.newPointerTypeNode(source, nodeFactory
								.newTypedefNameNode(nodeFactory
										.newIdentifierNode(source,
												"_kernelInstance"), null)));
		VariableDeclarationNode eDeclaration = nodeFactory
				.newVariableDeclarationNode(source, nodeFactory
						.newIdentifierNode(source, "e"), nodeFactory
						.newTypedefNameNode(nodeFactory.newIdentifierNode(
								source, "cudaEvent_t"), null));
		SequenceNode<VariableDeclarationNode> innerKernelFormals = nodeFactory
				.newSequenceNode(source, "innerKernelFormals",
						Arrays.asList(thisDeclaration, eDeclaration));
		FunctionDefinitionNode blockDefinition = buildBlockDefinition(body);
		FunctionCallNode waitInQueueCall = nodeFactory.newFunctionCallNode(
				source,
				this.identifierExpression(source, "_waitInQueue"),
				Arrays.asList(this.identifierExpression(source, "this"),
						this.identifierExpression(source, "e")), null);
		FunctionCallNode runProcsCall = nodeFactory.newFunctionCallNode(source,
				this.identifierExpression(source, "_runProcs"), Arrays.asList(
						this.identifierExpression(source, "gridDim"),
						this.identifierExpression(source, "_block")), null);
		FunctionCallNode kernelFinishCall = nodeFactory.newFunctionCallNode(
				source, this.identifierExpression(source, "_kernelFinish"),
				Arrays.asList(this.identifierExpression(source, "this")), null);
		CompoundStatementNode innerKernelBody = nodeFactory
				.newCompoundStatementNode(
						source,
						Arrays.asList(
								blockDefinition,
								nodeFactory
										.newExpressionStatementNode(waitInQueueCall),
								nodeFactory
										.newExpressionStatementNode(runProcsCall),
								nodeFactory
										.newExpressionStatementNode(kernelFinishCall)));
		FunctionDefinitionNode innerKernelDefinition = nodeFactory
				.newFunctionDefinitionNode(source, nodeFactory
						.newIdentifierNode(source, "_kernel"), nodeFactory
						.newFunctionTypeNode(source,
								nodeFactory.newVoidTypeNode(source),
								innerKernelFormals, false), null,
						innerKernelBody);
		return innerKernelDefinition;
	}

	protected FunctionDefinitionNode buildBlockDefinition(
			CompoundStatementNode body) {
		Source source = body.getSource();
		CompoundStatementNode threadBody = body.copy();
		DotNode blockDimX = nodeFactory.newDotNode(source,
				this.identifierExpression(source, "blockIdx"),
				nodeFactory.newIdentifierNode(source, "x"));
		DotNode blockDimY = nodeFactory.newDotNode(source,
				this.identifierExpression(source, "blockIdx"),
				nodeFactory.newIdentifierNode(source, "y"));
		DotNode blockDimZ = nodeFactory.newDotNode(source,
				this.identifierExpression(source, "blockIdx"),
				nodeFactory.newIdentifierNode(source, "z"));
		OperatorNode numThreads = nodeFactory.newOperatorNode(source,
				Operator.TIMES, Arrays.asList(nodeFactory.newOperatorNode(
						source, Operator.TIMES,
						Arrays.<ExpressionNode> asList(blockDimX, blockDimY)),
						blockDimZ));
		FunctionCallNode newGbarrier = nodeFactory.newFunctionCallNode(source,
				this.identifierExpression(source, "$gbarrier_create"), Arrays
						.asList(this.identifierExpression(source, "$here"),
								numThreads), null);
		VariableDeclarationNode gbarrierCreation = nodeFactory
				.newVariableDeclarationNode(source, nodeFactory
						.newIdentifierNode(source, "_block_barrier"),
						nodeFactory.newTypedefNameNode(nodeFactory
								.newIdentifierNode(source, "$gbarrier"), null),
						newGbarrier);
		List<BlockItemNode> sharedVars = this
				.extractSharedVariableDeclarations(threadBody);
		SequenceNode<VariableDeclarationNode> blockFormals = nodeFactory
				.newSequenceNode(source, "blockFormals", Arrays
						.asList(nodeFactory.newVariableDeclarationNode(source,
								nodeFactory.newIdentifierNode(source,
										"blockIdx"), nodeFactory
										.newTypedefNameNode(nodeFactory
												.newIdentifierNode(source,
														"uint3"), null))));
		FunctionDefinitionNode threadDefinition = this
				.buildThreadDefinition(threadBody);
		FunctionCallNode runProcsCall = nodeFactory.newFunctionCallNode(source,
				this.identifierExpression(source, "_runProcs"), Arrays.asList(
						this.identifierExpression(source, "blockDim"),
						this.identifierExpression(source, "_thread")), null);
		FunctionCallNode gbarrierDestruction = nodeFactory.newFunctionCallNode(
				source, this.identifierExpression(source, "$gbarrier_destroy"),
				Arrays.asList(this.identifierExpression(source,
						"_block_barrier")), null);
		List<BlockItemNode> blockBodyItems = new ArrayList<BlockItemNode>();
		blockBodyItems.add(gbarrierCreation);
		blockBodyItems.addAll(sharedVars);
		blockBodyItems.add(threadDefinition);
		blockBodyItems
				.add(nodeFactory.newExpressionStatementNode(runProcsCall));
		blockBodyItems.add(nodeFactory
				.newExpressionStatementNode(gbarrierDestruction));
		CompoundStatementNode blockBody = nodeFactory.newCompoundStatementNode(
				source, blockBodyItems);
		FunctionDefinitionNode blockDefinition = nodeFactory
				.newFunctionDefinitionNode(source, nodeFactory
						.newIdentifierNode(source, "_block"), nodeFactory
						.newFunctionTypeNode(source,
								nodeFactory.newVoidTypeNode(source),
								blockFormals, false), null, blockBody);
		return blockDefinition;
	}

	protected FunctionDefinitionNode buildThreadDefinition(
			CompoundStatementNode body) {
		Source source = body.getSource();
		SequenceNode<VariableDeclarationNode> threadFormals = nodeFactory
				.newSequenceNode(source, "threadFormals", Arrays
						.asList(nodeFactory.newVariableDeclarationNode(source,
								nodeFactory.newIdentifierNode(source,
										"threadIdx"), nodeFactory
										.newTypedefNameNode(nodeFactory
												.newIdentifierNode(source,
														"uint3"), null))));
		FunctionCallNode tid = nodeFactory.newFunctionCallNode(source, this
				.identifierExpression(source, "_index"), Arrays.asList(
				this.identifierExpression(source, "blockDim"),
				this.identifierExpression(source, "threadIdx")), null);
		FunctionCallNode newBarrier = nodeFactory.newFunctionCallNode(source,
				this.identifierExpression(source, "$barrier_create"), Arrays
						.asList(this.identifierExpression(source, "$here"),
								this.identifierExpression(source,
										"_block_barrier"), tid), null);
		VariableDeclarationNode barrierCreation = nodeFactory
				.newVariableDeclarationNode(source, nodeFactory
						.newIdentifierNode(source, "_b"), nodeFactory
						.newTypedefNameNode(nodeFactory.newIdentifierNode(
								source, "$gbarrier"), null), newBarrier);
		FunctionCallNode barrierDestruction = nodeFactory.newFunctionCallNode(
				source, this.identifierExpression(source, "$barrier_destroy"),
				Arrays.asList(this.identifierExpression(source, "_b")), null);
		List<BlockItemNode> threadBodyItems = new ArrayList<BlockItemNode>();
		threadBodyItems.add(barrierCreation);
		threadBodyItems.addAll(this.transformSyncThreadsCalls(body));
		threadBodyItems.add(nodeFactory
				.newExpressionStatementNode(barrierDestruction));
		CompoundStatementNode threadBody = nodeFactory
				.newCompoundStatementNode(source, threadBodyItems);
		FunctionDefinitionNode threadDefinition = nodeFactory
				.newFunctionDefinitionNode(source, nodeFactory
						.newIdentifierNode(source, "_thread"), nodeFactory
						.newFunctionTypeNode(source,
								nodeFactory.newVoidTypeNode(source),
								threadFormals, false), null, threadBody);
		return threadDefinition;
	}

	protected List<BlockItemNode> transformSyncThreadsCalls(
			CompoundStatementNode body) {
		Source source = body.getSource();
		List<BlockItemNode> transformedItems = new ArrayList<BlockItemNode>();
		ExpressionStatementNode barrierCall = nodeFactory
				.newExpressionStatementNode(nodeFactory.newFunctionCallNode(
						source,
						this.identifierExpression(source, "$barrier_call"),
						Arrays.asList(this.identifierExpression(source, "_b")),
						null));
		for (BlockItemNode item : body) {
			boolean added = false;
			if (item instanceof ExpressionStatementNode) {
				ExpressionNode itemExpr = ((ExpressionStatementNode) item)
						.getExpression();
				if (itemExpr instanceof FunctionCallNode) {
					FunctionCallNode call = (FunctionCallNode) itemExpr;
					ExpressionNode function = call.getFunction();
					if (function instanceof IdentifierExpressionNode
							&& call.getNumberOfArguments() == 0) {
						String functionName = ((IdentifierExpressionNode) function)
								.getIdentifier().name();
						if (functionName == "__synchthreads"
								&& call.getNumberOfArguments() == 0) {
							transformedItems.add(barrierCall.copy());
							added = false;
						}
					}
				}
			}
			if (!added)
				transformedItems.add(item);
		}
		return transformedItems;
	}
}
