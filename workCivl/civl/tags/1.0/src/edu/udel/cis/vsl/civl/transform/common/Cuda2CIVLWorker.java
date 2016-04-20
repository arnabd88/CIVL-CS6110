package edu.udel.cis.vsl.civl.transform.common;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode.NodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.CastNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.DotNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode.ExpressionKind;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CompoundStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ExpressionStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode.StatementKind;
import edu.udel.cis.vsl.abc.ast.node.IF.type.ArrayTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.FunctionTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode.TypeNodeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.PointerType;
import edu.udel.cis.vsl.abc.ast.type.IF.QualifiedObjectType;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.ast.type.IF.Type.TypeKind;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;

public class Cuda2CIVLWorker extends BaseWorker {

	private int tempVarNum;

	public Cuda2CIVLWorker(ASTFactory astFactory) {
		super("CUDAtoCIVLTransformer", astFactory);
		this.identifierPrefix = "$cuda_";
	}

	@Override
	public AST transform(AST ast) throws SyntaxException {
		SequenceNode<BlockItemNode> root = ast.getRootNode();

		ast.release();
		removeBuiltinDefinitions(root);
		translateCudaMallocCalls(root);
		translateKernelCalls(root);
		translateMainDefinition(root);
		translateKernelDefinitions(root);

		// root.prettyPrint(System.out);
		// System.out.println();
		return astFactory.newAST(root, ast.getSourceFiles());
	}

	protected String newTemporaryVariableName() {
		return "_t" + tempVarNum++;
	}

	protected void translateMainDefinition(ASTNode root) {
		for (ASTNode child : root.children()) {
			if (child == null)
				continue;

			if (child.nodeKind() == NodeKind.FUNCTION_DEFINITION) {
				FunctionDefinitionNode definition = (FunctionDefinitionNode) child;
				if (definition.getName() != null
						&& definition.getName().equals("main")) {
					root.setChild(child.childIndex(),
							mainDefinitionTransform(definition));
				}
			}
		}
	}

	protected void translateKernelDefinitions(ASTNode root) {
		for (ASTNode child : root.children()) {
			if (child == null)
				continue;

			if (child.nodeKind() == NodeKind.FUNCTION_DEFINITION) {
				FunctionDefinitionNode definition = (FunctionDefinitionNode) child;
				if (definition.hasGlobalFunctionSpecifier()) {
					root.setChild(child.childIndex(),
							kernelDefinitionTransform(definition));
				}

			}
		}
	}

	protected void translateCudaMallocCalls(ASTNode root) {
		for (ASTNode child : root.children()) {
			if (child == null)
				continue;

			if (child.nodeKind() == NodeKind.EXPRESSION) {
				ExpressionNode expression = (ExpressionNode) child;
				if (expression.expressionKind() == ExpressionKind.FUNCTION_CALL) {
					FunctionCallNode functionCall = (FunctionCallNode) expression;
					if (functionCall.getFunction().expressionKind() == ExpressionKind.IDENTIFIER_EXPRESSION) {
						IdentifierExpressionNode identifierExpression = (IdentifierExpressionNode) functionCall
								.getFunction();
						if (identifierExpression.getIdentifier().name()
								.equals("cudaMalloc")) {
							int index = functionCall.childIndex();
							root.setChild(index,
									cudaMallocTransform(functionCall));
							continue;
						}
					}
				}
			}

			translateCudaMallocCalls(child);
		}
	}

	protected void translateKernelCalls(ASTNode root) {
		for (ASTNode child : root.children()) {
			if (child == null)
				continue;

			if (child.nodeKind() == NodeKind.STATEMENT) {
				StatementNode statement = (StatementNode) child;
				if (statement.statementKind() == StatementKind.EXPRESSION) {
					ExpressionStatementNode expressionStatement = (ExpressionStatementNode) statement;
					ExpressionNode expression = expressionStatement
							.getExpression();
					if (expression.expressionKind() == ExpressionKind.FUNCTION_CALL) {
						FunctionCallNode functionCall = (FunctionCallNode) expression;
						if (functionCall.getNumberOfContextArguments() > 0) {
							root.setChild(statement.childIndex(),
									kernelCallTransform(functionCall));
							continue;
						}
					}
				}
			}

			translateKernelCalls(child);
		}
	}

	// translates "cudaMalloc( (void**) ptrPtr, size)" to
	// "*ptrPtr = (type)$malloc($root, size), cudaSuccess"
	// where "type" is the type of *ptrPtr
	protected ExpressionNode cudaMallocTransform(FunctionCallNode cudaMallocCall) {
		Source source = cudaMallocCall.getSource();
		// find the pointer
		ExpressionNode ptrPtr = cudaMallocCall.getArgument(0);
		while (ptrPtr instanceof CastNode) {
			ptrPtr = ((CastNode) ptrPtr).getArgument();
		}
		ExpressionNode size = cudaMallocCall.getArgument(1);
		// build lhs expression
		ExpressionNode assignLhs = nodeFactory.newOperatorNode(
				cudaMallocCall.getSource(), Operator.DEREFERENCE,
				Arrays.asList(ptrPtr.copy()));
		Type lhsType;
		if (ptrPtr.getInitialType().kind() == TypeKind.POINTER) {
			PointerType ptrType = (PointerType) ptrPtr.getInitialType();
			lhsType = ptrType.referencedType();
		} else {
			lhsType = ptrPtr.getInitialType();
		}
		// build rhs expression
		FunctionCallNode mallocCall = nodeFactory.newFunctionCallNode(source,
				this.identifierExpression(source, "$malloc"),
				Arrays.asList(nodeFactory.newHereNode(source), size.copy()),
				null);
		CastNode mallocCast = nodeFactory.newCastNode(source,
				this.typeNode(source, lhsType), mallocCall);
		// create assign node
		OperatorNode assignment = nodeFactory.newOperatorNode(
				cudaMallocCall.getSource(), Operator.ASSIGN,
				Arrays.asList(assignLhs, mallocCast));
		// create comma node
		ExpressionNode finalExpression = nodeFactory.newOperatorNode(source,
				Operator.COMMA, Arrays.asList(assignment, nodeFactory
				.newEnumerationConstantNode(nodeFactory
				.newIdentifierNode(source, "cudaSuccess"))));
		return finalExpression;
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

	protected FunctionDefinitionNode kernelDefinitionTransform(
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
		List<VariableDeclarationNode> newKernelFormalsList = new ArrayList<>();

		newKernelFormalsList.add(nodeFactory.newVariableDeclarationNode(source,
				this.identifier("gridDim"),
				nodeFactory.newTypedefNameNode(this.identifier("dim3"), null)));
		newKernelFormalsList.add(nodeFactory.newVariableDeclarationNode(source,
				this.identifier("blockDim"),
				nodeFactory.newTypedefNameNode(this.identifier("dim3"), null)));
		newKernelFormalsList
				.add(nodeFactory.newVariableDeclarationNode(
						source,
						this.identifier("memSize"),
						nodeFactory.newTypedefNameNode(
								this.identifier("size_t"), null)));
		newKernelFormalsList.add(nodeFactory.newVariableDeclarationNode(source,
				this.identifier("s"), nodeFactory.newTypedefNameNode(
						this.identifier("cudaStream_t"), null)));
		for (VariableDeclarationNode decl : oldDefinition.getTypeNode()
				.getParameters()) {
			newKernelFormalsList.add(decl.copy());
		}
		SequenceNode<VariableDeclarationNode> newKernelFormals = nodeFactory
				.newSequenceNode(source, "kernel formals", newKernelFormalsList);
		FunctionTypeNode newKernelType = nodeFactory.newFunctionTypeNode(
				source, oldDefinition.getTypeNode().getReturnType().copy(),
				newKernelFormals, true);
		FunctionDefinitionNode newKernel = nodeFactory
				.newFunctionDefinitionNode(source,
						nodeFactory.newIdentifierNode(source, newKernelName),
						newKernelType, null, newKernelBody);
		return newKernel;
	}

	protected List<VariableDeclarationNode> extractSharedVariableDeclarations(
			CompoundStatementNode statements) {
		List<VariableDeclarationNode> declarations = new ArrayList<>();
		for (BlockItemNode item : statements) {
			if (item instanceof VariableDeclarationNode) {
				VariableDeclarationNode variableDeclaration = (VariableDeclarationNode) item;
				if (variableDeclaration.hasSharedStorage()) {
					statements.removeChild(item.childIndex());
					variableDeclaration.setSharedStorage(false);
					declarations.add(variableDeclaration);
				}
			}
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
				this.identifierExpression(source, "blockDim"),
				nodeFactory.newIdentifierNode(source, "x"));
		DotNode blockDimY = nodeFactory.newDotNode(source,
				this.identifierExpression(source, "blockDim"),
				nodeFactory.newIdentifierNode(source, "y"));
		DotNode blockDimZ = nodeFactory.newDotNode(source,
				this.identifierExpression(source, "blockDim"),
				nodeFactory.newIdentifierNode(source, "z"));
		OperatorNode numThreads = nodeFactory.newOperatorNode(source,
				Operator.TIMES, Arrays.asList(nodeFactory.newOperatorNode(
						source, Operator.TIMES,
						Arrays.<ExpressionNode> asList(blockDimX, blockDimY)),
						blockDimZ));
		FunctionCallNode newGbarrier = nodeFactory.newFunctionCallNode(source,
				this.identifierExpression(source, "$gbarrier_create"),
				Arrays.asList(nodeFactory.newHereNode(source), numThreads),
				null);
		VariableDeclarationNode gbarrierCreation = nodeFactory
				.newVariableDeclarationNode(source, nodeFactory
						.newIdentifierNode(source, "_block_barrier"),
						nodeFactory.newTypedefNameNode(nodeFactory
								.newIdentifierNode(source, "$gbarrier"), null),
						newGbarrier);
		List<VariableDeclarationNode> sharedVars = this
				.extractSharedVariableDeclarations(threadBody);
		completeSharedExternArrays(sharedVars);
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

	protected void completeSharedExternArrays(
			List<VariableDeclarationNode> sharedVars) {
		for (VariableDeclarationNode node : sharedVars) {
			if (node.hasExternStorage()
					&& node.getTypeNode().kind() == TypeNodeKind.ARRAY) {
				ArrayTypeNode arrayType = (ArrayTypeNode) node.getTypeNode();
				if (arrayType.getExtent() == null) {
					arrayType.setExtent(this.identifierExpression("memSize"));
					node.setExternStorage(false);
				}
			}
		}
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
		VariableDeclarationNode tidDecl = nodeFactory
				.newVariableDeclarationNode(
						source,
						this.identifier("_tid"),
						nodeFactory.newBasicTypeNode(source, BasicTypeKind.INT),
						nodeFactory.newFunctionCallNode(source, this
								.identifierExpression(source, "_index"), Arrays
								.asList(this.identifierExpression(source,
										"blockDim"), this.identifierExpression(
										source, "threadIdx")), null));
		FunctionCallNode newBarrier = nodeFactory.newFunctionCallNode(source,
				this.identifierExpression(source, "$barrier_create"), Arrays
						.asList(nodeFactory.newHereNode(source),
								this.identifierExpression(source,
										"_block_barrier"), this
										.identifierExpression("_tid")), null);
		VariableDeclarationNode barrierCreation = nodeFactory
				.newVariableDeclarationNode(source, nodeFactory
						.newIdentifierNode(source, "_b"), nodeFactory
						.newTypedefNameNode(nodeFactory.newIdentifierNode(
								source, "$barrier"), null), newBarrier);
		FunctionCallNode barrierDestruction = nodeFactory.newFunctionCallNode(
				source, this.identifierExpression(source, "$barrier_destroy"),
				Arrays.asList(this.identifierExpression(source, "_b")), null);
		List<BlockItemNode> threadBodyItems = new ArrayList<BlockItemNode>();
		threadBodyItems.add(tidDecl);
		threadBodyItems.add(barrierCreation);
		for (BlockItemNode child : body) {
			if (child != null)
				threadBodyItems.add(child.copy());
		}
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

		FunctionCallNode barrierCall = nodeFactory.newFunctionCallNode(source,
				this.identifierExpression(source, "$barrier_call"),
				Arrays.asList(this.identifierExpression(source, "_b")), null);
		replaceSyncThreadsCalls(threadDefinition, barrierCall);
		return threadDefinition;
	}

	protected void replaceSyncThreadsCalls(ASTNode root,
			ExpressionNode replacement) {

		for (ASTNode child : root.children()) {
			if (child == null)
				continue;

			if (child instanceof ExpressionNode) {
				ExpressionNode itemExpr = (ExpressionNode) child;
				if (itemExpr instanceof FunctionCallNode) {
					FunctionCallNode call = (FunctionCallNode) itemExpr;
					ExpressionNode function = call.getFunction();
					if (function instanceof IdentifierExpressionNode) {
						String functionName = ((IdentifierExpressionNode) function)
								.getIdentifier().name();
						if (functionName.equals("__syncthreads")) {
							root.setChild(child.childIndex(),
									replacement.copy());
							continue;
						}
					}
				}
			}
			replaceSyncThreadsCalls(child, replacement);
		}
	}

	protected StatementNode kernelCallTransform(FunctionCallNode kernelCall) {
		Source source = kernelCall.getSource();
		List<VariableDeclarationNode> tempVarDecls = new ArrayList<>();
		List<ExpressionNode> newArgumentList = new ArrayList<>();
		for (int i = 0; i < 2; i++) {
			ExpressionNode arg = kernelCall.getContextArgument(i);
			Type argType = arg.getConvertedType();
			if (argType.kind() == TypeKind.QUALIFIED) {
				argType = ((QualifiedObjectType) argType).getBaseType();
			}
			if (argType.kind() == TypeKind.BASIC
					&& ((StandardBasicType) argType).getBasicTypeKind() == BasicTypeKind.INT) {

				String tmpVar = newTemporaryVariableName();
				ExpressionNode intConvertedToDim3 = nodeFactory
						.newFunctionCallNode(source,
								this.identifierExpression("_toDim3"),
								Arrays.asList(arg.copy()), null);
				tempVarDecls.add(nodeFactory.newVariableDeclarationNode(source,
						this.identifier(tmpVar), nodeFactory
								.newTypedefNameNode(this.identifier("dim3"),
										null), intConvertedToDim3));
				newArgumentList.add(this.identifierExpression(tmpVar));
			} else {
				newArgumentList.add(arg.copy());
			}
		}
		if (kernelCall.getNumberOfContextArguments() < 3) {
			try {
				newArgumentList.add(nodeFactory.newIntegerConstantNode(source,
						"0"));
			} catch (SyntaxException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		} else {
			newArgumentList.add(kernelCall.getContextArgument(2).copy());
		}
		if (kernelCall.getNumberOfContextArguments() < 4) {
			try {
				newArgumentList.add(nodeFactory.newIntegerConstantNode(source,
						"0"));
			} catch (SyntaxException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		} else {
			newArgumentList.add(kernelCall.getContextArgument(3));
		}
		for (int i = 0; i < kernelCall.getNumberOfArguments(); i++) {
			newArgumentList.add(kernelCall.getArgument(i).copy());
		}
		ExpressionNode newFunction;
		if (kernelCall.getFunction() instanceof IdentifierExpressionNode) {
			IdentifierExpressionNode identifierExpression = (IdentifierExpressionNode) kernelCall
					.getFunction();
			newFunction = this
					.identifierExpression(transformKernelName(identifierExpression
							.getIdentifier().name()));
		} else {
			newFunction = kernelCall.getFunction().copy();
		}
		FunctionCallNode newFunctionCall = nodeFactory.newFunctionCallNode(
				source, newFunction, newArgumentList, null);
		List<BlockItemNode> blockItems = new ArrayList<>();
		blockItems.addAll(tempVarDecls);
		blockItems.add(nodeFactory.newExpressionStatementNode(newFunctionCall));
		CompoundStatementNode replacementNode = nodeFactory
				.newCompoundStatementNode(source, blockItems);
		return replacementNode;
	}

	protected void removeBuiltinDefinitions(ASTNode root) {
		Set<String> builtinVariables = new HashSet<>(Arrays.asList("threadIdx",
				"blockIdx", "gridDim", "blockDim"));
		for (ASTNode child : root.children()) {
			if (child == null)
				continue;

			if (child.nodeKind() == NodeKind.VARIABLE_DECLARATION) {
				VariableDeclarationNode variableDeclaration = (VariableDeclarationNode) child;
				if (variableDeclaration.getIdentifier() != null
						&& builtinVariables.contains(variableDeclaration
								.getIdentifier().name())) {
					root.removeChild(child.childIndex());
					continue;
				}
			}

			removeBuiltinDefinitions(child);
		}
	}
}
