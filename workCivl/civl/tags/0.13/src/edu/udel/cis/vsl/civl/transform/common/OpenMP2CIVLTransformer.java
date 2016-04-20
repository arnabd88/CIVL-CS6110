package edu.udel.cis.vsl.civl.transform.common;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.NoSuchElementException;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.entity.IF.Variable;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode.NodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.ExternalDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.PairNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.compound.CompoundInitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.compound.DesignationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.InitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.CompoundLiteralNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IntegerConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.label.SwitchLabelNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpForNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpReductionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpSymbolReductionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpSyncNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CivlForNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CompoundStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.DeclarationListNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ExpressionStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ForLoopInitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ForLoopNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.IfNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.ast.node.common.omp.CommonOmpForNode;
import edu.udel.cis.vsl.abc.ast.node.common.omp.CommonOmpParallelNode;
import edu.udel.cis.vsl.abc.ast.node.common.omp.CommonOmpWorkshareNode;
import edu.udel.cis.vsl.abc.ast.type.IF.ArrayType;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;

import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.civl.util.IF.Triple;

/**
 * OpenMP2CIVLTransformer transforms an AST of an OpenMP program into an AST of
 * an equivalent CIVL-C program. See {@linkplain #transform(AST)}.
 * 
 * @author Michael Rogers
 * 
 */
public class OpenMP2CIVLTransformer extends CIVLBaseTransformer {

	/* ************************** Public Static Fields *********************** */
	/**
	 * The code (short name) of this transformer.
	 */
	public final static String CODE = "openmp";

	/**
	 * The long name of the transformer.
	 */
	public static String LONG_NAME = "OpenMPTransformer";

	/**
	 * The description of this transformer.
	 */
	public static String SHORT_DESCRIPTION = "transforms C/OpenMP program to CIVL-C";

	/* ************************** Private Static Fields ********************** */

	/**
	 * The name of the identifier of the $omp_gteam variable in the final CIVL
	 * program.
	 */
	private static String GTEAM = "gteam";

	/**
	 * The name of the identifier of the $omp_team variable in the final CIVL
	 * program.
	 */
	private static String TEAM = "team";

	/**
	 * The name of $omp_gteam type in the final CIVL-C program.
	 */
	private static String GTEAM_TYPE = "$omp_gteam";

	/**
	 * The name of $omp_team type in the final CIVL-C program.
	 */
	private static String TEAM_TYPE = "$omp_team";

	/**
	 * The name of the function to create a new $omp_gws object in the final
	 * CIVL-C program.
	 */
	private static String GTEAM_CREATE = "$omp_gteam_create";

	/**
	 * The name of the function to create a new $omp_ws object in the final
	 * CIVL-C program.
	 */
	private static String TEAM_CREATE = "$omp_team_create";

	/**
	 * The name of $omp_gshared type in the final CIVL-C program.
	 */
	private static String GSHARED_TYPE = "$omp_gshared";

	/**
	 * The name of $omp_shared type in the final CIVL-C program.
	 */
	private static String SHARED_TYPE = "$omp_shared";

	/**
	 * The name of the function to create a new $omp_gshared object in the final
	 * CIVL-C program.
	 */
	private static String GSHARED_CREATE = "$omp_gshared_create";

	/**
	 * The name of the function to create a new $omp_shared object in the final
	 * CIVL-C program.
	 */
	private static String SHARED_CREATE = "$omp_shared_create";

	/**
	 * The name of the input variable denoting the number of OpenMP threads in
	 * the final CIVL-C program.
	 */
	private static String NTHREADS = "_nthreads";

	/**
	 * The name of the input variable denoting the number of OpenMP threads in
	 * the final CIVL-C program.
	 */
	private static String THREADMAX = "THREAD_MAX";

	/**
	 * The name of the variable denoting the thread number in the CIVL_C
	 * program.
	 */
	private static String TID = "_tid";

	private int tmpCount = 0;

	private ArrayList<Triple<String, StatementNode, String>> sharedReplaced = new ArrayList<Triple<String, StatementNode, String>>();

	private ArrayList<String> criticalNames = new ArrayList<String>();

	/* **************************** Instant Fields ************************* */

	/**
	 * There are new nodes created by the transformer, other than parsing from
	 * some source file. All new nodes share the same source.
	 */
	private Source source;

	/* ****************************** Constructor ************************** */
	/**
	 * Creates a new instance of OpenMP2CIVLTransformer.
	 * 
	 * @param astFactory
	 *            The ASTFactory that will be used to create new nodes.
	 */
	public OpenMP2CIVLTransformer(ASTFactory astFactory) {
		super(CODE, LONG_NAME, SHORT_DESCRIPTION, astFactory);
	}

	/* *************************** Private Methods ************************* */

	/**
	 * Creates the declaration node for the input variable
	 * <code>THREAD_MAX</code>.
	 * 
	 * @return The declaration node of the input variable
	 *         <code>THREAD_MAX</code>.
	 */
	private VariableDeclarationNode threadMaxDeclaration() {
		TypeNode nthreadsType = nodeFactory.newBasicTypeNode(source,
				BasicTypeKind.INT);

		nthreadsType.setInputQualified(true);
		return nodeFactory.newVariableDeclarationNode(source,
				nodeFactory.newIdentifierNode(source, THREADMAX), nthreadsType);
	}

	/**
	 * Creates the declaration node for the variable <code>gteam</code> , which
	 * is of <code>$omp_gteam</code> type and has an initializer to call
	 * <code>$omp_gteam_create()</code>. That is:
	 * <code>$omp_gteam gteam = $omp_gteam_create($here, NTHREADS)</code> .
	 * 
	 * @return The declaration node of the variable <code>gteam</code>.
	 */
	private VariableDeclarationNode gteamDeclaration() {
		TypeNode gteamType;
		ExpressionNode gteamCreate;

		gteamType = nodeFactory.newTypedefNameNode(
				nodeFactory.newIdentifierNode(source, GTEAM_TYPE), null);
		gteamCreate = nodeFactory.newFunctionCallNode(
				source,
				this.identifierExpression(source, GTEAM_CREATE),
				Arrays.asList(nodeFactory.newHereNode(source),
						this.identifierExpression(source, NTHREADS)), null);
		return nodeFactory.newVariableDeclarationNode(source,
				nodeFactory.newIdentifierNode(source, GTEAM), gteamType,
				gteamCreate);
	}

	/**
	 * Creates the declaration node for the variable <code>team</code> , which
	 * is of <code>$omp_team</code> type and has an initializer to call
	 * <code>$omp_team_create()</code>. That is:
	 * <code>$omp_team team = $omp_team_create($here, gteam, _tid)</code> .
	 * 
	 * @return The declaration node of the variable <code>_gws</code>.
	 */
	private VariableDeclarationNode teamDeclaration() {
		TypeNode teamType;
		ExpressionNode teamCreate;

		teamType = nodeFactory.newTypedefNameNode(
				nodeFactory.newIdentifierNode(source, TEAM_TYPE), null);
		teamCreate = nodeFactory.newFunctionCallNode(
				source,
				this.identifierExpression(source, TEAM_CREATE),
				Arrays.asList(nodeFactory.newHereNode(source),
						this.identifierExpression(source, GTEAM),
						this.identifierExpression(source, TID)), null);
		return nodeFactory.newVariableDeclarationNode(source,
				nodeFactory.newIdentifierNode(source, TEAM), teamType,
				teamCreate);
	}

	private VariableDeclarationNode gsharedDeclaration(String variable) {
		TypeNode gsharedType;
		ExpressionNode gsharedCreate;

		ExpressionNode addressOf = nodeFactory.newOperatorNode(source,
				Operator.ADDRESSOF,
				Arrays.asList(this.identifierExpression(source, variable)));

		gsharedType = nodeFactory.newTypedefNameNode(
				nodeFactory.newIdentifierNode(source, GSHARED_TYPE), null);
		gsharedCreate = nodeFactory.newFunctionCallNode(source, this
				.identifierExpression(source, GSHARED_CREATE), Arrays.asList(
				this.identifierExpression(source, GTEAM), addressOf), null);
		return nodeFactory.newVariableDeclarationNode(source,
				nodeFactory.newIdentifierNode(source, variable + "_gshared"),
				gsharedType, gsharedCreate);
	}

	private VariableDeclarationNode sharedDeclaration(String variable) {
		TypeNode sharedType;
		ExpressionNode sharedCreate;

		sharedType = nodeFactory.newTypedefNameNode(
				nodeFactory.newIdentifierNode(source, SHARED_TYPE), null);
		ExpressionNode addressOfLocalVar = nodeFactory.newOperatorNode(source,
				Operator.ADDRESSOF,
				Arrays.asList(this.identifierExpression(source, variable + "_local")));
		ExpressionNode addressOfStatusVar = nodeFactory.newOperatorNode(source,
				Operator.ADDRESSOF,
				Arrays.asList(this.identifierExpression(source, variable + "_status")));
		sharedCreate = nodeFactory
				.newFunctionCallNode(source, this.identifierExpression(source,
						SHARED_CREATE), Arrays.asList(this
						.identifierExpression(source, TEAM), this
						.identifierExpression(source, variable + "_gshared"), 
						addressOfLocalVar, addressOfStatusVar),
						null);
		return nodeFactory.newVariableDeclarationNode(source,
				nodeFactory.newIdentifierNode(source, variable + "_shared"),
				sharedType, sharedCreate);
	}

	private ExpressionStatementNode destroy(String type, String object) {
		ExpressionNode function = this.identifierExpression(source, "$omp_"
				+ type + "_destroy");

		return nodeFactory.newExpressionStatementNode(nodeFactory
				.newFunctionCallNode(source, function, Arrays.asList(this
						.identifierExpression(source, object)), null));
	}

	private ExpressionStatementNode barrierAndFlush(String object) {
		ExpressionNode function = this.identifierExpression(source,
				"$omp_barrier_and_flush");

		return nodeFactory.newExpressionStatementNode(nodeFactory
				.newFunctionCallNode(source, function, Arrays.asList(this
						.identifierExpression(source, object)), null));
	}

	private ExpressionStatementNode write(ExpressionNode variable, String sharedName) {
		ExpressionNode function = this.identifierExpression(source,
				"$omp_write");
		ExpressionNode addressOfVar = nodeFactory.newOperatorNode(source,
				Operator.ADDRESSOF,
				Arrays.asList(variable));
		ExpressionNode addressOfTmp = nodeFactory.newOperatorNode(source,
				Operator.ADDRESSOF,
				Arrays.asList(this.identifierExpression(source, "tmp"+ String.valueOf(tmpCount))));
		return nodeFactory
				.newExpressionStatementNode(nodeFactory.newFunctionCallNode(
						source, function, Arrays.asList(
								this.identifierExpression(source, sharedName
										+ "_shared"), addressOfVar,
								addressOfTmp), null));
	}

	private ExpressionStatementNode read(ExpressionNode parent, String sharedName,
			String tmpName) {
		ExpressionNode function = this
				.identifierExpression(source, "$omp_read");
		ExpressionNode addressOfVar = nodeFactory.newOperatorNode(source,
				Operator.ADDRESSOF,
				Arrays.asList(parent));
		ExpressionNode addressOfTmp = nodeFactory.newOperatorNode(source,
				Operator.ADDRESSOF,
				Arrays.asList(this.identifierExpression(source, tmpName)));
		return nodeFactory
				.newExpressionStatementNode(nodeFactory.newFunctionCallNode(
						source, function, Arrays.asList(
								this.identifierExpression(source, sharedName
										+ "_shared"), addressOfVar,
								addressOfTmp), null));
	}

	private ExpressionStatementNode applyAssoc(String variable, String operation) {
		ExpressionNode function = this.identifierExpression(source,
				"$omp_apply_assoc");
		ExpressionNode addressOfVar = nodeFactory.newOperatorNode(source,
				Operator.ADDRESSOF, Arrays.asList(this.identifierExpression(
						source, "_" + variable)));
		if (operation.equals("PLUSEQ")) {
			operation = "CIVL_SUM";
		}
		return nodeFactory.newExpressionStatementNode(nodeFactory
				.newFunctionCallNode(source, function,
						Arrays.asList(
								this.identifierExpression(source, variable
										+ "_shared"),
								this.identifierExpression(source, operation),
								addressOfVar), null));
	}

	/* ********************* Methods From BaseTransformer ****************** */

	/**
	 * 
	 * 
	 */
	@Override
	public AST transform(AST ast) throws SyntaxException {
		SequenceNode<ExternalDefinitionNode> root = ast.getRootNode();
		AST newAst;
		List<ExternalDefinitionNode> externalList;
		VariableDeclarationNode threadMax;
		SequenceNode<ExternalDefinitionNode> newRootNode;
		List<ExternalDefinitionNode> includedNodes = new ArrayList<>();
		List<VariableDeclarationNode> mainParameters = new ArrayList<>();
		int count;
		Triple<List<ExternalDefinitionNode>, List<ExternalDefinitionNode>, List<VariableDeclarationNode>> result;

		this.source = root.getSource();
		assert this.astFactory == ast.getASTFactory();
		assert this.nodeFactory == astFactory.getNodeFactory();
		ast.release();

		// declaring $input int THREAD_MAX;
		threadMax = this.threadMaxDeclaration();

		// if (!this.inputVariableNames.contains(THREADMAX)) {
		// throw new SyntaxException(
		// "Please specify the number of processes (e.g., -inputTHREAD_MAX=5)",
		// source);
		// }

		replaceOMPPragmas(root, null, null, null, null);

		result = this.program(root);
		includedNodes = result.second;
		mainParameters = result.third;

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
		externalList.add(threadMax);
		for (String name : criticalNames) {
			externalList.add(nodeFactory.newVariableDeclarationNode(source,
					nodeFactory.newIdentifierNode(source, name),
					nodeFactory.newBasicTypeNode(source, BasicTypeKind.BOOL),
					nodeFactory.newBooleanConstantNode(source, false)));
		}
		externalList.addAll(result.first);
		newRootNode = nodeFactory.newSequenceNode(null, "TranslationUnit",
				externalList);
		newAst = astFactory.newAST(newRootNode);

		return newAst;
	}

	@SuppressWarnings("unchecked")
	private void replaceOMPPragmas(ASTNode node,
			SequenceNode<IdentifierExpressionNode> privateIDs,
			SequenceNode<IdentifierExpressionNode> sharedIDs,
			SequenceNode<IdentifierExpressionNode> reductionIDs,
			SequenceNode<IdentifierExpressionNode> firstPrivateIDs)
			throws SyntaxException {
		if (node instanceof CommonOmpParallelNode) {
			List<BlockItemNode> items;
			CompoundStatementNode pragmaBody;
			VariableDeclarationNode gteamVar;
			SequenceNode<IdentifierExpressionNode> sharedList;
			SequenceNode<IdentifierExpressionNode> privateList;
			SequenceNode<IdentifierExpressionNode> firstPrivateList;
			SequenceNode<IdentifierExpressionNode> reductionList = null;
			SequenceNode<OmpReductionNode> ompReductionNode;
			Iterable<ASTNode> children;
			items = new LinkedList<>();
			children = node.children();

			// int _nthreads = 1+$choose_int(THREAD_MAX);
			VariableDeclarationNode nthreads;
			ExpressionNode add;

			add = nodeFactory.newOperatorNode(source, Operator.PLUS, Arrays
					.asList(nodeFactory.newIntegerConstantNode(source, "1"),
							nodeFactory.newFunctionCallNode(source,
									this.identifierExpression(source,
											"$choose_int"), Arrays.asList(this
											.identifierExpression(source,
													THREADMAX)), null)));

			nthreads = nodeFactory.newVariableDeclarationNode(source,
					nodeFactory.newIdentifierNode(source, "_nthreads"),
					nodeFactory.newBasicTypeNode(source, BasicTypeKind.INT),
					add);
			items.add(nthreads);

			VariableDeclarationNode threadRange;
			threadRange = nodeFactory.newVariableDeclarationNode(source,
					nodeFactory.newIdentifierNode(source, "thread_range"),
					nodeFactory.newRangeTypeNode(source),
					nodeFactory.newRegularRangeNode(source, nodeFactory
							.newIntegerConstantNode(source, "0"), nodeFactory
							.newOperatorNode(source, Operator.MINUS, Arrays
									.asList(this.identifierExpression(source,
											"_nthreads"),
											nodeFactory.newIntegerConstantNode(
													source, "1")))));
			items.add(threadRange);
			
			List<PairNode<DesignationNode, InitializerNode>> initList = new ArrayList<PairNode<DesignationNode, InitializerNode>>();
			initList.add(nodeFactory.newPairNode(source, (DesignationNode) null, (InitializerNode)this.identifierExpression(source, "thread_range")));
			CompoundInitializerNode temp = nodeFactory.newCompoundInitializerNode(source, initList);
			CompoundLiteralNode cln = nodeFactory.newCompoundLiteralNode(source, nodeFactory.newDomainTypeNode(source), temp);
			

			VariableDeclarationNode loopDomain;
			loopDomain = nodeFactory.newVariableDeclarationNode(
					source,
					nodeFactory.newIdentifierNode(source, "dom"),
					nodeFactory.newDomainTypeNode(source),
					nodeFactory.newCastNode(source,
							nodeFactory.newDomainTypeNode(source),
							cln));
			items.add(loopDomain);

			// Declaring $omp_gteam gteam = $omp_gteam_create($here, nthreads);
			gteamVar = this.gteamDeclaration();
			items.add(gteamVar);

			sharedList = ((CommonOmpParallelNode) node).sharedList();
			privateList = ((CommonOmpParallelNode) node).privateList();
			firstPrivateList = ((CommonOmpParallelNode) node)
					.firstprivateList();

			OmpSymbolReductionNode reductionNode = null;
			ompReductionNode = ((CommonOmpParallelNode) node).reductionList();
			if (ompReductionNode != null) {
				node.removeChild(6);
				reductionNode = (OmpSymbolReductionNode) ompReductionNode
						.child(0);
				reductionList = (SequenceNode<IdentifierExpressionNode>) reductionNode
						.child(0);
			}

			// Declaring $omp_gshared x_gshared = $omp_gshared_create(gteam, &x)
			// for each shared variable "x"
			if (sharedList != null) {
				node.removeChild(0);
				for (ASTNode child : sharedList.children()) {
					VariableDeclarationNode gsharedVar;
					IdentifierNode c = ((IdentifierExpressionNode) child)
							.getIdentifier();

					gsharedVar = this.gsharedDeclaration(c.name());
					items.add(gsharedVar);
				}
			}
			CivlForNode cfn;
			ForLoopInitializerNode initializerNode;

			initializerNode = nodeFactory.newForLoopInitializerNode(source,
					Arrays.asList(nodeFactory.newVariableDeclarationNode(
							source, nodeFactory.newIdentifierNode(source,
									"_tid"), nodeFactory.newBasicTypeNode(
									source, BasicTypeKind.INT))));

			List<BlockItemNode> parForItems = new LinkedList<>();

			// $omp_team team = $omp_team_create($here, gteam, _tid);
			parForItems.add(teamDeclaration());
			
			if(sharedList != null){
				for(ASTNode child : sharedList.children()) {
					VariableDeclarationNode localSharedVar;
					VariableDeclarationNode statusSharedVar;
					
					
					IdentifierNode c = (IdentifierNode)child.child(0);
					
//					TypeNode privateType = ((VariableDeclarationNode) c
//							.getEntity().getFirstDeclaration()).getTypeNode()
//							.copy();
					TypeNode privateType = ((VariableDeclarationNode) ((Variable) c
							.getEntity()).getFirstDeclaration()).getTypeNode().copy();
					IdentifierNode localSharedIdentifer = nodeFactory
							.newIdentifierNode(source, c.name() + "_local");
					IdentifierNode statusSharedIdentifer = nodeFactory
							.newIdentifierNode(source, c.name() + "_status");

					localSharedVar = nodeFactory.newVariableDeclarationNode(
							source, localSharedIdentifer, privateType);
					statusSharedVar = nodeFactory.newVariableDeclarationNode(
							source, statusSharedIdentifer, nodeFactory.newBasicTypeNode(
									source, BasicTypeKind.INT));
					parForItems.add(localSharedVar);
					parForItems.add(statusSharedVar);
					
				}
			}

			// Declare $omp_shared x_shared = $omp_shared_create(team,
			// x_gshared, void *local, void, *status)
			// for each shared variable "x"
			if (sharedList != null) {
				for (ASTNode child : sharedList.children()) {
					VariableDeclarationNode sharedVar;
					IdentifierNode c = ((IdentifierExpressionNode) child)
							.getIdentifier();

					sharedVar = this.sharedDeclaration(c.name());
					parForItems.add(sharedVar);
				}
			}

			// Add firstprivate variable declarations
			if (firstPrivateList != null) {
				node.removeChild(2);
				for (ASTNode child : firstPrivateList.children()) {
					VariableDeclarationNode firstPrivate = addPrivateVariable(
							(IdentifierExpressionNode) child, "first");
					parForItems.add(firstPrivate);
				}
			}

			// Add reduction variable declarations
			if (reductionList != null) {
				for (ASTNode child : reductionList.children()) {
					VariableDeclarationNode localPrivate = addPrivateVariable(
							(IdentifierExpressionNode) child, "reduction");
					parForItems.add(localPrivate);
				}
			}

			// Declare local copies of the private variables
			if (privateList != null) {
				node.removeChild(1);
				for (ASTNode child : privateList.children()) {
					VariableDeclarationNode localPrivate = addPrivateVariable(
							(IdentifierExpressionNode) child, "regular");
					parForItems.add(localPrivate);
				}
			}

			int i = 0;
			for (ASTNode child : children) {
				node.removeChild(i);
				parForItems.add((BlockItemNode) child);
				i++;
			}

			// $omp_barrier_and_flush(team);
			parForItems.add(barrierAndFlush(TEAM));

			// $omp_shared_destroy(x_shared);
			// for each shared variable "x"
			if (sharedList != null) {
				for (ASTNode child : sharedList.children()) {
					IdentifierNode c = ((IdentifierExpressionNode) child)
							.getIdentifier();

					parForItems.add(destroy("shared", c.name() + "_shared"));
				}
			}

			// $omp_team_destroy(team);
			parForItems.add(destroy(TEAM, TEAM));

			StatementNode parForBody;
			parForBody = nodeFactory.newCompoundStatementNode(source,
					parForItems);

			cfn = nodeFactory.newCivlForNode(source, true,
					(DeclarationListNode) initializerNode,
					this.identifierExpression(source, "dom"), parForBody, null);

			items.add(cfn);

			// $omp_shared_destroy(x_gshared);
			// for each shared variable "x"
			if (sharedList != null) {
				for (ASTNode child : sharedList.children()) {
					IdentifierNode c = ((IdentifierExpressionNode) child)
							.getIdentifier();

					items.add(destroy("gshared", c.name() + "_gshared"));
				}
			}

			// $omp_gteam_destroy(gteam);
			items.add(destroy("gteam", "gteam"));

			pragmaBody = nodeFactory.newCompoundStatementNode(source, items);

			int index = node.childIndex();
			ASTNode parent = node.parent();
			parent.setChild(index, pragmaBody);
			children = pragmaBody.children();

			for (ASTNode child : children) {
				replaceOMPPragmas(child, privateList, sharedList,
						reductionList, firstPrivateList);
			}
		} else if (node instanceof CommonOmpForNode) {
			ForLoopInitializerNode initializerNode;
			SequenceNode<OmpReductionNode> ompReductionNode;
			SequenceNode<IdentifierExpressionNode> reductionList = null;
			List<BlockItemNode> items;
			List<BlockItemNode> forItems;
			CompoundStatementNode pragmaBody;
			Iterable<ASTNode> children = node.children();
			items = new LinkedList<>();
			forItems = new LinkedList<>();
			VariableDeclarationNode loopDomain;
			int collapseLevel = ((OmpForNode) node).collapse();
			ASTNode body = null;
			ArrayList<Pair<ASTNode, ASTNode>> ranges = new ArrayList<Pair<ASTNode, ASTNode>>();
			ArrayList<IdentifierNode> loopVariables = new ArrayList<IdentifierNode>();
			SequenceNode<IdentifierExpressionNode> firstPrivateList;

			ForLoopNode currentLoop = null;
			OperatorNode initializer;
			OperatorNode condition;
			OmpSymbolReductionNode reductionNode = null;
			ompReductionNode = ((CommonOmpForNode) node).reductionList();
			if (ompReductionNode != null) {
				node.removeChild(6);
				reductionNode = (OmpSymbolReductionNode) ompReductionNode
						.child(0);
				reductionList = (SequenceNode<IdentifierExpressionNode>) reductionNode
						.child(0);
			}

			firstPrivateList = ((CommonOmpForNode) node).firstprivateList();

			for (int i = 0; i < collapseLevel; i++) {
				if (i == 0) {
					currentLoop = (ForLoopNode) node.child(7);
					body = currentLoop.child(1);
				} else {
					currentLoop = (ForLoopNode) currentLoop.getBody();
					body = currentLoop.child(1);
				}
				initializer = (OperatorNode) currentLoop.child(3);
				condition = (OperatorNode) currentLoop.getCondition();

				ranges.add(new Pair<ASTNode, ASTNode>(initializer.child(1),
						condition.child(1)));
				loopVariables.add((IdentifierNode) initializer.child(0)
						.child(0));
			}

			int rangeNumber = 0;
			for(Pair<ASTNode, ASTNode> pair: ranges){
				VariableDeclarationNode threadRange;
				threadRange = nodeFactory.newVariableDeclarationNode(source, 
						nodeFactory.newIdentifierNode(source, "r" + Integer.toString(rangeNumber+1)), 
						nodeFactory.newRangeTypeNode(source), 
						nodeFactory.newRegularRangeNode(source, (ExpressionNode) pair.left.copy(), (ExpressionNode) pair.right.copy()));
				items.add(threadRange);
				rangeNumber++;
			}
			List<PairNode<DesignationNode, InitializerNode>> initList = new ArrayList<PairNode<DesignationNode, InitializerNode>>();;
			for(int k=1; k<rangeNumber+1; k++){
				initList.add(nodeFactory.newPairNode(source, (DesignationNode) null, (InitializerNode)this.identifierExpression(source, "r" + Integer.toString(k))));
			}
			CompoundInitializerNode temp = nodeFactory.newCompoundInitializerNode(source, initList);
			CompoundLiteralNode cln = nodeFactory.newCompoundLiteralNode(source, nodeFactory.newDomainTypeNode(source, nodeFactory.newIntegerConstantNode(source, Integer.toString(rangeNumber))), temp);
			if(body instanceof CompoundStatementNode){
				children = body.children();
			} else {
				ArrayList<ASTNode> tempList = new ArrayList<ASTNode>();
				tempList.add(body);
				Iterable<ASTNode> tempIt = tempList;
				children = (Iterable<ASTNode>) tempIt;
				
			}
			
			loopDomain = nodeFactory.newVariableDeclarationNode(source,
					nodeFactory.newIdentifierNode(source, "loop_domain"),
					nodeFactory.newDomainTypeNode(source), nodeFactory.newCastNode(source, nodeFactory.newDomainTypeNode(source), cln));
			items.add(loopDomain);
			ExpressionNode ompArriveLoop = nodeFactory.newCastNode(source,
					nodeFactory.newDomainTypeNode(source,
							nodeFactory.newIntegerConstantNode(source, Integer.toString(collapseLevel))),
					nodeFactory.newFunctionCallNode(source, this
							.identifierExpression(source, "$omp_arrive_loop"),
							Arrays.asList(this.identifierExpression(source,
									TEAM), this.identifierExpression(source,
									"loop_domain"), nodeFactory.newIntegerConstantNode(source, "0")), null));

			IntegerConstantNode domainLevel;
			if (collapseLevel == 1) {
				domainLevel = nodeFactory.newIntegerConstantNode(source, "1");
			} else {
				domainLevel = nodeFactory.newIntegerConstantNode(source,
						String.valueOf(collapseLevel));
			}

			VariableDeclarationNode myIters;

			myIters = nodeFactory.newVariableDeclarationNode(source,
					nodeFactory.newIdentifierNode(source, "my_iters"),
					nodeFactory.newDomainTypeNode(source, domainLevel),
					ompArriveLoop);

			items.add(myIters);

			// Add firstprivate variable declarations
			if (firstPrivateList != null) {
				node.removeChild(2);
				for (ASTNode child : firstPrivateList.children()) {
					VariableDeclarationNode firstPrivate = addPrivateVariable(
							(IdentifierExpressionNode) child, "first");
					items.add(firstPrivate);
				}
				firstPrivateIDs = firstPrivateList;
			}

			// Add reduction variable declarations
			if (reductionList != null) {
				for (ASTNode child : reductionList.children()) {
					VariableDeclarationNode localPrivate = addPrivateVariable(
							(IdentifierExpressionNode) child, "reduction");
					items.add(localPrivate);
				}
				reductionIDs = reductionList;
			}
			CivlForNode cfn;

			List<VariableDeclarationNode> declarations = new ArrayList<VariableDeclarationNode>();
			for (IdentifierNode var : loopVariables) {
				declarations
						.add(nodeFactory.newVariableDeclarationNode(source, var
								.copy(), nodeFactory.newBasicTypeNode(source,
								BasicTypeKind.INT)));
			}

			initializerNode = nodeFactory.newForLoopInitializerNode(source,
					declarations);

			for (int i = 0; i < collapseLevel; i++) {
				if (i == 0) {
					currentLoop = (ForLoopNode) node.child(7);
				} else {
					currentLoop = (ForLoopNode) currentLoop.getBody();
				}
			}

			int i = 0;
			for (ASTNode child : children) {
				if(body instanceof CompoundStatementNode){
					body.removeChild(i);
				} else {
					ASTNode bodyParent = body.parent();
					int bodyIndex = body.childIndex();
					bodyParent.removeChild(bodyIndex);
				}
				
				forItems.add((BlockItemNode) child);
				i++;
			}

			StatementNode forBody;
			forBody = nodeFactory.newCompoundStatementNode(source, forItems);

			cfn = nodeFactory.newCivlForNode(
					source,
					false,
					(DeclarationListNode) initializerNode,
					nodeFactory.newIdentifierExpressionNode(source,
							nodeFactory.newIdentifierNode(source, "my_iters")),
					forBody, null);

			items.add(cfn);

			if (reductionList != null) {
				for (ASTNode child : reductionList.children()) {
					String name = ((IdentifierNode) child.child(0)).name();
					String operator = reductionNode.operator().name();
					items.add(applyAssoc(name, operator));
				}
			}

			// $barrier_and_flush(team);
			if (!((CommonOmpForNode) node).nowait()) {
				items.add(barrierAndFlush(TEAM));
			}

			pragmaBody = nodeFactory.newCompoundStatementNode(source, items);
			children = pragmaBody.children();
			int index = node.childIndex();
			ASTNode parent = node.parent();
			parent.setChild(index, pragmaBody);

			for (ASTNode child : children) {
				replaceOMPPragmas(child, privateIDs, sharedIDs, reductionIDs,
						firstPrivateIDs);
			}

		} else if (node instanceof OmpSyncNode) {
			String syncKind = ((OmpSyncNode) node).ompSyncNodeKind().toString();
			CompoundStatementNode body;
			LinkedList<BlockItemNode> items = new LinkedList<>();
			if (syncKind.equals("MASTER")) {
				List<ExpressionNode> operands = new ArrayList<ExpressionNode>();
				operands.add(nodeFactory.newIdentifierExpressionNode(source,
						nodeFactory.newIdentifierNode(source, "_tid")));
				operands.add(nodeFactory.newIntegerConstantNode(source, "0"));
				int i = 0;
				for (ASTNode child : node.children()) {
					node.removeChild(i);
					items.add((BlockItemNode) child);
					i++;
				}
				body = nodeFactory.newCompoundStatementNode(source, items);
				IfNode ifStatement = nodeFactory.newIfNode(source, nodeFactory
						.newOperatorNode(source, Operator.EQUALS, operands),
						body);
				int index = node.childIndex();
				ASTNode parent = node.parent();
				parent.setChild(index, ifStatement);
			} else if (syncKind.equals("BARRIER")) {
				ExpressionStatementNode barrierAndFlush = barrierAndFlush(TEAM);
				int index = node.childIndex();
				ASTNode parent = node.parent();
				parent.setChild(index, barrierAndFlush);
			} else if (syncKind.equals("CRITICAL")) {
				IdentifierNode criticalIDName = ((OmpSyncNode) node).criticalName();
				String criticalName = null;
				if(criticalIDName != null){
					criticalName = "_critical_" + criticalIDName.name();
					node.removeChild(9);
				} else {
					criticalName = "_critical_noname";
				}
				
				ExpressionNode notCritical = nodeFactory.newOperatorNode(
						source, Operator.NOT, Arrays.asList(this
								.identifierExpression(source, criticalName)));
				ExpressionStatementNode criticalTrue = nodeFactory
						.newExpressionStatementNode(nodeFactory
								.newOperatorNode(source, Operator.ASSIGN,
										Arrays.asList(
												this.identifierExpression(
														source, criticalName),
												nodeFactory
														.newBooleanConstantNode(
																source, true))));

				items.add(nodeFactory.newWhenNode(source, notCritical,
						criticalTrue));
				int i = 0;
				for (ASTNode child : node.children()) {
					node.removeChild(i);
					items.add((BlockItemNode) child);
					i++;
				}
				ExpressionStatementNode criticalFalse = nodeFactory
						.newExpressionStatementNode(nodeFactory
								.newOperatorNode(
										source,
										Operator.ASSIGN,
										Arrays.asList(
												this.identifierExpression(
														source, criticalName),
												nodeFactory
														.newBooleanConstantNode(
																source, false))));
				items.add(criticalFalse);

				body = nodeFactory.newCompoundStatementNode(source, items);
				criticalNames.add(criticalName);
				int index = node.childIndex();
				ASTNode parent = node.parent();
				parent.setChild(index, body);
			}
		} else if (node instanceof CommonOmpWorkshareNode) {
			Iterable<ASTNode> children = node.children();
			String workshareKind = ((CommonOmpWorkshareNode) node)
					.ompWorkshareNodeKind().toString();
			CompoundStatementNode body;
			LinkedList<BlockItemNode> items = new LinkedList<>();
			if (workshareKind.equals("SECTIONS")) {
				privateIDs = ((CommonOmpWorkshareNode) node).privateList();
				firstPrivateIDs = ((CommonOmpWorkshareNode) node)
						.firstprivateList();
				int numberSections = 0;
				CompoundStatementNode pragmaBody = (CompoundStatementNode) node
						.child(7);
				ArrayList<LinkedList<BlockItemNode>> sectionsChildren = new ArrayList<LinkedList<BlockItemNode>>();
				for (ASTNode child : pragmaBody.children()) {
					if (child instanceof CommonOmpWorkshareNode) {
						if (((CommonOmpWorkshareNode) child)
								.ompWorkshareNodeKind().toString()
								.equals("SECTION")) {
							LinkedList<BlockItemNode> sectionItems = new LinkedList<>();
							int i = 0;
							for (ASTNode sectionChild : child.children()) {
								child.removeChild(i);
								sectionItems.add((BlockItemNode) sectionChild);
								i++;
							}
							sectionsChildren.add(sectionItems);
							numberSections++;
						}
					}
				}

				ExpressionNode ompArriveSections = nodeFactory
						.newFunctionCallNode(source, this.identifierExpression(
								source, "$omp_arrive_sections"), Arrays.asList(
								this.identifierExpression(source, TEAM),
								this.identifierExpression(source,
										String.valueOf(numberSections))), null);

				VariableDeclarationNode my_secs;
				my_secs = nodeFactory
						.newVariableDeclarationNode(source, nodeFactory
								.newIdentifierNode(source, "my_secs"),
								nodeFactory.newDomainTypeNode(source,
										nodeFactory.newIntegerConstantNode(
												source, "1")),
								ompArriveSections);
				items.add(my_secs);

				// Declare local copies of the private variables
				if (privateIDs != null) {
					node.removeChild(1);
					for (ASTNode child : privateIDs.children()) {
						VariableDeclarationNode localPrivate = addPrivateVariable(
								(IdentifierExpressionNode) child, "regular");
						items.add(localPrivate);
					}
				}

				// Add firstprivate variable declarations
				if (firstPrivateIDs != null) {
					node.removeChild(2);
					for (ASTNode child : firstPrivateIDs.children()) {
						VariableDeclarationNode firstPrivate = addPrivateVariable(
								(IdentifierExpressionNode) child, "first");
						items.add(firstPrivate);
					}
				}

				CivlForNode cfn;

				List<BlockItemNode> forItems = new LinkedList<>();

				// for loop;
				ForLoopInitializerNode initializerNode = nodeFactory
						.newForLoopInitializerNode(source, Arrays
								.asList(nodeFactory.newVariableDeclarationNode(
										source, nodeFactory.newIdentifierNode(
												source, "i"), nodeFactory
												.newBasicTypeNode(source,
														BasicTypeKind.INT))));

				StatementNode forBody;
				StatementNode switchBody;
				List<BlockItemNode> switchItems = new LinkedList<>();
				int caseNumber = 0;
				for (LinkedList<BlockItemNode> tempChildren : sectionsChildren) {
					StatementNode caseBody;
					List<BlockItemNode> caseItems = tempChildren;
					caseItems.add(nodeFactory.newBreakNode(source));
					caseBody = nodeFactory.newCompoundStatementNode(source,
							caseItems);
					SwitchLabelNode labelDecl = nodeFactory
							.newCaseLabelDeclarationNode(source, nodeFactory
									.newIntegerConstantNode(source,
											String.valueOf(caseNumber)),
									caseBody);
					switchItems.add(nodeFactory.newLabeledStatementNode(source,
							labelDecl, caseBody));
				}
				switchBody = nodeFactory.newCompoundStatementNode(source,
						switchItems);
				forItems.add(nodeFactory.newSwitchNode(source,
						this.identifierExpression(source, "i"), switchBody));
				forBody = nodeFactory
						.newCompoundStatementNode(source, forItems);

				cfn = nodeFactory.newCivlForNode(source, true,
						(DeclarationListNode) initializerNode, nodeFactory
								.newIdentifierExpressionNode(source,
										nodeFactory.newIdentifierNode(source,
												"my_secs")), forBody, null);
				items.add(cfn);

				if (!((CommonOmpWorkshareNode) node).nowait()) {
					items.add(barrierAndFlush(TEAM));
				}

				CompoundStatementNode sectionBody = nodeFactory
						.newCompoundStatementNode(source, items);

				int index = node.childIndex();
				ASTNode parent = node.parent();
				parent.setChild(index, sectionBody);

				for (ASTNode child : children) {
					replaceOMPPragmas(child, privateIDs, sharedIDs,
							reductionIDs, firstPrivateIDs);
				}

			}
			if (workshareKind.equals("SINGLE")) {

				ExpressionNode arriveSingle = nodeFactory
						.newFunctionCallNode(source, this.identifierExpression(
								source, "$omp_arrive_single"),
								Arrays.asList(this.identifierExpression(source,
										TEAM)), null);
				items.add(nodeFactory
						.newVariableDeclarationNode(source, nodeFactory
								.newIdentifierNode(source, "owner"),
								nodeFactory.newBasicTypeNode(source,
										BasicTypeKind.INT), arriveSingle));

				List<ExpressionNode> operands = new ArrayList<ExpressionNode>();
				operands.add(this.identifierExpression(source, "owner"));
				operands.add(this.identifierExpression(source, "_tid"));
				int i = 0;
				CompoundStatementNode ifBody;
				LinkedList<BlockItemNode> ifItems = new LinkedList<>();
				for (ASTNode child : node.children()) {
					node.removeChild(i);
					ifItems.add((BlockItemNode) child);
					i++;
				}
				ifBody = nodeFactory.newCompoundStatementNode(source, ifItems);

				IfNode ifStatement = nodeFactory.newIfNode(source, nodeFactory
						.newOperatorNode(source, Operator.EQUALS, operands),
						ifBody);
				items.add(ifStatement);
				items.add(barrierAndFlush(TEAM));
				body = nodeFactory.newCompoundStatementNode(source, items);

				int index = node.childIndex();
				ASTNode parent = node.parent();
				parent.setChild(index, body);

				for (ASTNode child : children) {
					replaceOMPPragmas(child, privateIDs, sharedIDs,
							reductionIDs, firstPrivateIDs);
				}

			}
		} else if (node instanceof IdentifierNode) {
			if (privateIDs != null) {
				for (ASTNode child : privateIDs.children()) {
					IdentifierNode c = ((IdentifierExpressionNode) child)
							.getIdentifier();
					if (c.name().equals(((IdentifierNode) node).name())) {
						((IdentifierNode) node).setName("_"
								+ ((IdentifierNode) node).name());
					}
				}
			}
			if (firstPrivateIDs != null) {
				for (ASTNode child : privateIDs.children()) {
					IdentifierNode c = ((IdentifierExpressionNode) child)
							.getIdentifier();
					if (c.name().equals(((IdentifierNode) node).name())) {
						((IdentifierNode) node).setName("_"
								+ ((IdentifierNode) node).name());
					}
				}
			}
			if (reductionIDs != null) {
				for (ASTNode child : reductionIDs.children()) {
					IdentifierNode c = ((IdentifierExpressionNode) child)
							.getIdentifier();
					if (c.name().equals(((IdentifierNode) node).name())) {
						((IdentifierNode) node).setName("_"
								+ ((IdentifierNode) node).name());
					}
				}
			}
			if (sharedIDs != null
					&& ((IdentifierNode) node).getEntity() != null) {
				for (ASTNode child : sharedIDs.children()) {
					IdentifierNode c = ((IdentifierExpressionNode) child)
							.getIdentifier();
					if (c.name().equals(((IdentifierNode) node).name())) {
						ASTNode parent = getParentOfID((IdentifierNode) node);
						boolean sameName = false;
						for (Triple<String, StatementNode, String> tempName : sharedReplaced) {
							if (tempName.first.equals(((IdentifierNode) node)
									.name())) {
								if (tempName.second.equals(parent)) {
									sameName = true;
									((IdentifierNode) node)
											.setName(tempName.third);
								}
							}
						}
						if (!sameName) {
							sharedRead((IdentifierNode) node,
									(StatementNode) parent, privateIDs, sharedIDs, reductionIDs,
									firstPrivateIDs);
						}


					}
				}
			}

		} else if (node instanceof OperatorNode && sharedIDs != null
				&& ((OperatorNode) node).getOperator().toString()
						.equals("ASSIGN")) {
			ArrayList<OperatorNode> assignedToVars = new ArrayList<OperatorNode>();
			assignedToVars.add((OperatorNode) node);
			ASTNode rhs = node.child(1);
			do{
				if(rhs instanceof OperatorNode && ((OperatorNode) node.child(1)).getOperator().toString().equals("ASSIGN")){
					assignedToVars.add((OperatorNode) rhs);
					rhs = rhs.child(1);
				} else {
					rhs = null;
				}
			} while(rhs != null);

			ExpressionStatementNode temp = containsSharedWrite(
					assignedToVars, privateIDs, sharedIDs, reductionIDs,
					firstPrivateIDs);
			if(temp == null){
				replaceOMPPragmas(node.child(1), privateIDs, sharedIDs,
						reductionIDs, firstPrivateIDs);
			} else {
				OperatorNode initializer = (OperatorNode) temp.getExpression();
				while(initializer.child(1) instanceof OperatorNode && initializer.getOperator().toString().equals("ASSIGN")){
					initializer = (OperatorNode) initializer.child(1);
				}
					replaceOMPPragmas(initializer, privateIDs, sharedIDs,
							reductionIDs, firstPrivateIDs);

			}

		} else if (node != null) {
			Iterable<ASTNode> children = node.children();
			for (ASTNode child : children) {
				replaceOMPPragmas(child, privateIDs, sharedIDs, reductionIDs,
						firstPrivateIDs);
			}
		}

	}

	private VariableDeclarationNode addPrivateVariable(
			IdentifierExpressionNode node, String privateKind)
			throws SyntaxException {
		VariableDeclarationNode privateVariable;

		IdentifierNode c = node.getIdentifier();
		TypeNode privateType = ((VariableDeclarationNode) ((Variable) c
				.getEntity()).getFirstDeclaration()).getTypeNode().copy();
		IdentifierNode privateIdentifer = nodeFactory.newIdentifierNode(source,
				"_" + c.name());
		if (privateKind.equals("first")) {
			privateVariable = nodeFactory.newVariableDeclarationNode(source,
					privateIdentifer, privateType,
					this.identifierExpression(source, c.name()));
		} else if (privateKind.equals("reduction")) {
			privateVariable = nodeFactory.newVariableDeclarationNode(source,
					privateIdentifer, privateType,
					nodeFactory.newIntegerConstantNode(source, "0"));
		} else {
			privateVariable = nodeFactory.newVariableDeclarationNode(source,
					privateIdentifer, privateType);
		}
		return privateVariable;
	}

	private ASTNode getParentOfID(IdentifierNode node) {
		ASTNode parent = node.parent();
		while (!(parent instanceof StatementNode)) {
			parent = parent.parent();
		}
		return parent;
	}

	private CompoundStatementNode sharedRead(IdentifierNode node,
			StatementNode parentStatement, SequenceNode<IdentifierExpressionNode> privateIDs, SequenceNode<IdentifierExpressionNode> sharedIDs, SequenceNode<IdentifierExpressionNode> reductionIDs, SequenceNode<IdentifierExpressionNode> firstPrivateIDs) throws SyntaxException, NoSuchElementException {
		List<BlockItemNode> items = new LinkedList<>();
		CompoundStatementNode bodyRead;

		VariableDeclarationNode temp;
		Type currentType = ((Variable) node.getEntity()).getType();
		int nodesDeep = 0;
		while (currentType instanceof ArrayType) {
			currentType = ((ArrayType) currentType).getElementType();
			nodesDeep++;
		}
		BasicTypeKind baseTypeKind = ((StandardBasicType) currentType)
				.getBasicTypeKind();
		IdentifierNode tempID = nodeFactory.newIdentifierNode(source, "tmp"
				+ String.valueOf(tmpCount));
		temp = nodeFactory.newVariableDeclarationNode(source, tempID, nodeFactory.newBasicTypeNode(source,
				baseTypeKind));

		items.add(temp);
		ASTNode parentOfID = null;
		String nodeName = node.name();
		node.setName(node.name() + "_local");
		if (nodesDeep == 0) {
			parentOfID = node.parent();
			items.add(read((ExpressionNode) parentOfID.copy(), nodeName,
					"tmp" + String.valueOf(tmpCount)));
		} else {
			parentOfID = node.parent();
			while (nodesDeep > 0) {
				parentOfID = parentOfID.parent();
				nodesDeep--;
			}

			if(parentOfID instanceof OperatorNode){
				checkArrayIndices((OperatorNode) parentOfID, privateIDs, sharedIDs, reductionIDs,
						firstPrivateIDs);
			}
			items.add(read((ExpressionNode)parentOfID.copy(), nodeName,
					"tmp" + String.valueOf(tmpCount)));

			
		}

		String origName = node.name();
		ASTNode tempParent = parentOfID.parent();
		int nodeIndex = parentOfID.childIndex();
		tempParent.setChild(nodeIndex, this.identifierExpression(source, "tmp" + String.valueOf(tmpCount)));
		//node.setName("tmp" + String.valueOf(tmpCount));
		Triple<String, StatementNode, String> tempTriple = new Triple<>(
				origName, parentStatement, "tmp" + String.valueOf(tmpCount));
		sharedReplaced.add(tempTriple);
		tmpCount++;
		int index = parentStatement.childIndex();
		ASTNode parent = parentStatement.parent();
		parent.removeChild(index);
		items.add(parentStatement);

		bodyRead = nodeFactory.newCompoundStatementNode(source, items);
		parent.setChild(index, bodyRead);
		return bodyRead;
	}

	private ExpressionStatementNode containsSharedWrite(ArrayList<OperatorNode> assignedToVars,
			SequenceNode<IdentifierExpressionNode> privateIDs, SequenceNode<IdentifierExpressionNode> sharedIDs, SequenceNode<IdentifierExpressionNode> reductionIDs, SequenceNode<IdentifierExpressionNode> firstPrivateIDs) throws SyntaxException, NoSuchElementException {

		ArrayList<IdentifierNode> nodeID = new ArrayList<IdentifierNode>();
		for(OperatorNode op : assignedToVars){
			ASTNode nodeChild0 = op.child(0);
			if(nodeChild0 instanceof IdentifierExpressionNode){
				nodeID.add(((IdentifierExpressionNode) nodeChild0).getIdentifier());
			} else if(op.child(0) instanceof OperatorNode){
				while(nodeChild0 instanceof OperatorNode){
					nodeChild0 = nodeChild0.child(0);
				}
				nodeID.add(((IdentifierExpressionNode) nodeChild0).getIdentifier());
			}
		}
		List<BlockItemNode> items = new LinkedList<>();
		int nodesDeep = 0;
		int count = 0;
		int j = assignedToVars.size();
		ArrayList<VariableDeclarationNode> tempVarsAdded = new ArrayList<VariableDeclarationNode>();
		VariableDeclarationNode temp = null;
		ExpressionNode initializer = (ExpressionNode) assignedToVars.get(j-1).removeChild(1);
		for(IdentifierNode currentNodeID : nodeID){
			for (ASTNode child : sharedIDs.children()) {
				IdentifierNode c = ((IdentifierExpressionNode) child)
						.getIdentifier();
				if (c.name().equals(currentNodeID.name())) {
					Type currentType = ((Variable) currentNodeID.getEntity()).getType();
					nodesDeep = 0;
					while (currentType instanceof ArrayType) {
						currentType = ((ArrayType) currentType).getElementType();
						nodesDeep++;
					}

					BasicTypeKind baseTypeKind = ((StandardBasicType) currentType)
							.getBasicTypeKind();
					IdentifierNode tempID = nodeFactory.newIdentifierNode(source, "tmp" + String.valueOf(tmpCount + count));

					temp = nodeFactory.newVariableDeclarationNode(source, tempID, nodeFactory.newBasicTypeNode(source,
							baseTypeKind));
					tempVarsAdded.add(temp);
					items.add(temp); 
					count++;
				}
			}
		}
		ExpressionStatementNode assignmentOfTemp = null;
		if(!items.isEmpty()){
			count = 0;
			OperatorNode currentOp = null;
			for(int i = nodeID.size(); i > 0; i--){
				if(i == nodeID.size()){
					currentOp = nodeFactory.newOperatorNode(source, Operator.ASSIGN, 
							Arrays.asList(this.identifierExpression(source, "tmp" + String.valueOf(tmpCount + count)), initializer));
				} else {
					currentOp = nodeFactory.newOperatorNode(source, Operator.ASSIGN, 
							Arrays.asList(this.identifierExpression(source, "tmp" + String.valueOf(tmpCount + count)), currentOp));
				}
				count++;
			}
			assignmentOfTemp = nodeFactory.newExpressionStatementNode(currentOp);
			items.add(assignmentOfTemp);
		}
		
		
		
		for(IdentifierNode currentNodeID : nodeID){
			for (ASTNode child : sharedIDs.children()) {
				IdentifierNode c = ((IdentifierExpressionNode) child)
						.getIdentifier();
				if (c.name().equals(currentNodeID.name())) {

					ASTNode parentOfID = null;
					String nodeName = currentNodeID.name();
					currentNodeID.setName(currentNodeID.name() + "_local");
					if (nodesDeep == 0) {
						parentOfID = currentNodeID.parent();
						items.add(write((ExpressionNode) parentOfID.copy(), nodeName));
					} else {
						parentOfID = currentNodeID.parent();
						while (nodesDeep > 0) {
							parentOfID = parentOfID.parent();
							nodesDeep--;
						}

						if(parentOfID instanceof OperatorNode){
							checkArrayIndices((OperatorNode) parentOfID, privateIDs, sharedIDs, reductionIDs,
									firstPrivateIDs);
						}
						items.add(write((ExpressionNode)parentOfID.copy(), nodeName));
					}
					tmpCount++;


				}
			}
		}
		if(!items.isEmpty()){
			CompoundStatementNode bodyWrite;
			bodyWrite = nodeFactory.newCompoundStatementNode(source,
					items);
			ASTNode expNode = assignedToVars.get(0).parent();
			int index = expNode.childIndex();
			ASTNode parent = expNode.parent();
			parent.setChild(index, bodyWrite);
		}
		if(items.isEmpty() && initializer != null){
			assignedToVars.get(j-1).setChild(1, initializer);
		}
		return assignmentOfTemp;
	}
	
	private void checkArrayIndices(OperatorNode op, SequenceNode<IdentifierExpressionNode> privateIDs, SequenceNode<IdentifierExpressionNode> sharedIDs, 
			SequenceNode<IdentifierExpressionNode> reductionIDs, SequenceNode<IdentifierExpressionNode> firstPrivateIDs) throws SyntaxException, NoSuchElementException{
		replaceOMPPragmas(op.child(1), privateIDs, sharedIDs, reductionIDs,
				firstPrivateIDs);
		ASTNode lhs = op.child(0);
		while(lhs instanceof OperatorNode){
			replaceOMPPragmas(lhs.child(1), privateIDs, sharedIDs, reductionIDs,
					firstPrivateIDs);
			lhs = lhs.child(0);
		}
	}

	private Triple<List<ExternalDefinitionNode>, List<ExternalDefinitionNode>, List<VariableDeclarationNode>> program(
			SequenceNode<ExternalDefinitionNode> root) {
		List<ExternalDefinitionNode> includedNodes = new ArrayList<>();
		List<VariableDeclarationNode> vars = new ArrayList<>();
		List<ExternalDefinitionNode> items;
		int number;
		items = new LinkedList<>();
		number = root.numChildren();
		for (int i = 0; i < number; i++) {
			ExternalDefinitionNode child = root.getSequenceChild(i);
			String sourceFile;

			if (child == null)
				continue;
			sourceFile = child.getSource().getFirstToken().getSourceFile()
					.getName();
			root.removeChild(i);
			if (sourceFile.equals("omp.cvl")) {
				includedNodes.add(child);
			} else if (sourceFile.endsWith(".cvh")
					|| sourceFile.equals("comm.cvl")
					|| sourceFile.equals("civlmpi.cvl")
					|| sourceFile.equals("omp.cvl")
					|| sourceFile.equals("civlc.cvl")
					|| sourceFile.equals("concurrency.cvl")
					|| sourceFile.equals("stdio.cvl")
					|| sourceFile.equals("pthread.cvl")
					|| sourceFile.equals("string.cvl"))
				includedNodes.add(child);
			else if (sourceFile.endsWith(".h")) {
				if (child.nodeKind() == NodeKind.VARIABLE_DECLARATION) {
					VariableDeclarationNode variableDeclaration = (VariableDeclarationNode) child;
					if (sourceFile.equals("stdio.h"))
						// keep variable declaration nodes from stdio, i.e.,
						// stdout, stdin, etc.
						items.add(variableDeclaration);
					else
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
				items.add( child);
			}
		}
		return new Triple<>(items, includedNodes, vars);
	}
}
