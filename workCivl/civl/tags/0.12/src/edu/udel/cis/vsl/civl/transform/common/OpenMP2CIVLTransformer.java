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
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IntegerConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.label.SwitchLabelNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpSyncNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CivlForNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CompoundStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.DeclarationListNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ExpressionStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ForLoopInitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.IfNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.ast.node.common.CommonIdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.common.omp.CommonOmpForNode;
import edu.udel.cis.vsl.abc.ast.node.common.omp.CommonOmpParallelNode;
import edu.udel.cis.vsl.abc.ast.node.common.omp.CommonOmpWorkshareNode;
import edu.udel.cis.vsl.abc.ast.type.IF.ArrayType;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.util.IF.Triple;

/**
 * OpenMP2CIVLTransformer transforms an AST of an OpenMP program into an AST of an
 * equivalent CIVL-C program. See {@linkplain #transform(AST)}. 
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
	public OpenMP2CIVLTransformer(ASTFactory astFactory,
			List<String> inputVariables, CIVLConfiguration config) {
		super(CODE, LONG_NAME, SHORT_DESCRIPTION, astFactory, inputVariables,
				config);
	}

	/* *************************** Private Methods ************************* */

	/**
	 * Creates the declaration node for the input variable <code>THREAD_MAX</code>.
	 * 
	 * @return The declaration node of the input variable <code>THREAD_MAX</code>.
	 */
	private VariableDeclarationNode threadMaxDeclaration() {
		TypeNode nthreadsType = nodeFactory.newBasicTypeNode(source,
				BasicTypeKind.INT);

		nthreadsType.setInputQualified(true);
		return nodeFactory.newVariableDeclarationNode(source,
				nodeFactory.newIdentifierNode(source, THREADMAX), nthreadsType);
	}

	/**
	 * Creates the declaration node for the variable <code>gteam</code> ,
	 * which is of <code>$omp_gteam</code> type and has an initializer to call
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
	 * Creates the declaration node for the variable <code>team</code> ,
	 * which is of <code>$omp_team</code> type and has an initializer to call
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
						this.identifierExpression(source,  TID)), null);
		return nodeFactory.newVariableDeclarationNode(source,
				nodeFactory.newIdentifierNode(source, TEAM), teamType,
				teamCreate);
	}

	private VariableDeclarationNode gsharedDeclaration(String variable) {
		TypeNode gsharedType;
		ExpressionNode gsharedCreate;

		ExpressionNode addressOf = nodeFactory.newOperatorNode(source,
				Operator.ADDRESSOF, Arrays.asList(this
						.identifierExpression(source, variable)));
		
		gsharedType = nodeFactory.newTypedefNameNode(
				nodeFactory.newIdentifierNode(source, GSHARED_TYPE), null);
		gsharedCreate = nodeFactory.newFunctionCallNode(
				source,
				this.identifierExpression(source, GSHARED_CREATE),
				Arrays.asList(this.identifierExpression(source, GTEAM), 
						addressOf), null);
		return nodeFactory.newVariableDeclarationNode(source,
				nodeFactory.newIdentifierNode(source, variable + "_gshared"), gsharedType,
				gsharedCreate);
	}

	private VariableDeclarationNode sharedDeclaration(String variable) {
		TypeNode sharedType;
		ExpressionNode sharedCreate;

		sharedType = nodeFactory.newTypedefNameNode(
				nodeFactory.newIdentifierNode(source, SHARED_TYPE), null);
		sharedCreate = nodeFactory.newFunctionCallNode(
				source,
				this.identifierExpression(source, SHARED_CREATE),
				Arrays.asList(this.identifierExpression(source, TEAM), 
						this.identifierExpression(source,  variable + "_gshared")), null);
		return nodeFactory.newVariableDeclarationNode(source,
				nodeFactory.newIdentifierNode(source, variable + "_shared"), sharedType,
				sharedCreate);
	}

	private ExpressionStatementNode destroy(String type, String object) {
		ExpressionNode function = this.identifierExpression(source, "$omp_" + type + "_destroy");

		return nodeFactory.newExpressionStatementNode(nodeFactory
				.newFunctionCallNode(source, function, Arrays.asList(this
						.identifierExpression(source, object)), null));
	}
	
	private ExpressionStatementNode barrierAndFlush(String object) {
		ExpressionNode function = this.identifierExpression(source, "$omp_barrier_and_flush");

		return nodeFactory.newExpressionStatementNode(nodeFactory
				.newFunctionCallNode(source, function, Arrays.asList(this
						.identifierExpression(source, object)), null));
	}
	
	private ExpressionStatementNode write(String variable, String sharedName) {
		ExpressionNode function = this.identifierExpression(source, "$omp_write");
		ExpressionNode addressOfVar = nodeFactory.newOperatorNode(source,
				Operator.ADDRESSOF, Arrays.asList(this
						.identifierExpression(source, variable)));
		ExpressionNode addressOfTmp = nodeFactory.newOperatorNode(source,
				Operator.ADDRESSOF, Arrays.asList(this
						.identifierExpression(source, "tmp")));
		return nodeFactory.newExpressionStatementNode(nodeFactory
				.newFunctionCallNode(source, function, Arrays.asList(this
						.identifierExpression(source, sharedName + "_shared"), addressOfVar, addressOfTmp), null));
	}
	
	private ExpressionStatementNode read(String variable, String sharedName) {
		ExpressionNode function = this.identifierExpression(source, "$omp_read");
		ExpressionNode addressOfVar = nodeFactory.newOperatorNode(source,
				Operator.ADDRESSOF, Arrays.asList(this
						.identifierExpression(source, variable)));
		ExpressionNode addressOfTmp = nodeFactory.newOperatorNode(source,
				Operator.ADDRESSOF, Arrays.asList(this
						.identifierExpression(source, "tmp")));
		return nodeFactory.newExpressionStatementNode(nodeFactory
				.newFunctionCallNode(source, function, Arrays.asList(this
						.identifierExpression(source, sharedName + "_shared"), addressOfVar, addressOfTmp), null));
	}

	/* ********************* Methods From BaseTransformer ****************** */

	/**
	 * 
	 * 
	 */
	@SuppressWarnings("unchecked")
	@Override
	public AST transform(AST ast) throws SyntaxException {
		ASTNode root = ast.getRootNode();
		AST newAst;
		List<ASTNode> externalList;
		VariableDeclarationNode threadMax;
		SequenceNode<ASTNode> newRootNode;
		List<ASTNode> includedNodes = new ArrayList<ASTNode>();
		List<VariableDeclarationNode> mainParameters = new ArrayList<>();
		int count;
		Triple<List<ASTNode>, List<ASTNode>, List<VariableDeclarationNode>> result;

		this.source = root.getSource();
		assert this.astFactory == ast.getASTFactory();
		assert this.nodeFactory == astFactory.getNodeFactory();
		ast.release();

		// declaring $input int THREAD_MAX;
		threadMax = this.threadMaxDeclaration();

		if (!this.inputVariableNames.contains(THREADMAX)) {
			throw new SyntaxException(
					"Please specify the number of processes (e.g., -inputTHREAD_MAX=5)"
					, source);
		}

		replaceOMPPragmas(root, null, null);

		result = this.program((SequenceNode<ASTNode>) root);
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
		externalList.addAll(result.first);
		newRootNode = nodeFactory.newSequenceNode(null, "TranslationUnit",
				externalList);
		newAst = astFactory.newAST(newRootNode);

		return newAst;
	}

	private void replaceOMPPragmas(ASTNode node, 
			SequenceNode<IdentifierExpressionNode> privateIDs, 
			SequenceNode<IdentifierExpressionNode> sharedIDs) throws SyntaxException {
		if (node instanceof CommonOmpParallelNode) {
			List<BlockItemNode> items;
			CompoundStatementNode pragmaBody;
			VariableDeclarationNode gteamVar;
			SequenceNode<IdentifierExpressionNode> sharedList;
			SequenceNode<IdentifierExpressionNode> privateList;
			Iterable<ASTNode> children;
			items = new LinkedList<>();
			children = node.children();

			// int _nthreads = 1+$choose_int(THREAD_MAX);
			VariableDeclarationNode nthreads;
			ExpressionNode add;

			add = nodeFactory.newOperatorNode(source, Operator.PLUS, Arrays.asList(nodeFactory.newIntegerConstantNode(source, "1"), 
					nodeFactory
					.newFunctionCallNode(source, this.identifierExpression(source,"$choose_int"),
							Arrays.asList(this.identifierExpression(source, THREADMAX)), null)));

			nthreads = nodeFactory.newVariableDeclarationNode(source,
					nodeFactory.newIdentifierNode(source, "_nthreads"), nodeFactory.newBasicTypeNode(source, BasicTypeKind.INT),
					add);
			items.add(nthreads);
			
			VariableDeclarationNode loopDomain;
			loopDomain = nodeFactory.newVariableDeclarationNode(source,
					nodeFactory.newIdentifierNode(source, "loop_domain"), 
					nodeFactory.newDomainTypeNode(source));
			items.add(loopDomain);

			//Declaring $omp_gteam gteam = $omp_gteam_create($here, nthreads);
			gteamVar = this.gteamDeclaration();
			items.add(gteamVar);

			sharedList = ((CommonOmpParallelNode) node).sharedList();
			if(sharedList != null){
				node.removeChild(0);
			}

			privateList = ((CommonOmpParallelNode) node).privateList();
			if(privateList != null){
				node.removeChild(1);
			}

			//Declaring $omp_gshared x_gshared = $omp_gshared_create(gteam, &x)
			//for each shared variable "x"
			for(ASTNode child : sharedList.children()){
				VariableDeclarationNode gsharedVar;
				IdentifierNode c = ((IdentifierExpressionNode) child).getIdentifier();

				gsharedVar = this.gsharedDeclaration(c.name());
				items.add(gsharedVar);
			}
			CivlForNode cfn;
			ForLoopInitializerNode initializerNode;
	
			initializerNode = nodeFactory.newForLoopInitializerNode(source,
					Arrays.asList(nodeFactory.newVariableDeclarationNode(
							source, nodeFactory.newIdentifierNode(source,
									"_tid"), nodeFactory.newBasicTypeNode(
											source, BasicTypeKind.INT))));
			
			List<BlockItemNode> parForItems = new LinkedList<>();
			
			//$omp_team team = $omp_team_create($here, gteam, _tid);
			parForItems.add(teamDeclaration());
			
			//Declare $omp_shared x_shared = $omp_shared_create(team, x_gshared)
			//for each shared variable "x"
			if(sharedList != null){
				for(ASTNode child : sharedList.children()){
					VariableDeclarationNode sharedVar;
					IdentifierNode c = ((IdentifierExpressionNode) child).getIdentifier();

					sharedVar = this.sharedDeclaration(c.name());
					parForItems.add(sharedVar);
				}
			}
			
			//Declare local copies of the private variables
			if(privateList != null){
				for(ASTNode child : privateList.children()){
					VariableDeclarationNode localPrivate;

					IdentifierNode c = ((IdentifierExpressionNode) child).getIdentifier();
					TypeNode privateType = ((VariableDeclarationNode) c.getEntity().getFirstDeclaration()).getTypeNode().copy();
					IdentifierNode privateIdentifer = nodeFactory.newIdentifierNode(source, "_" + c.name());
					localPrivate = nodeFactory.newVariableDeclarationNode(source,
							privateIdentifer, privateType);
					parForItems.add(localPrivate);
				}
			}

			int i = 0;
			for(ASTNode child : children) {
				node.removeChild(i);
				parForItems.add((BlockItemNode) child);
				i++;
			}
			
			//$omp_barrier_and_flush(team); 
			parForItems.add(barrierAndFlush(TEAM));
			
			// $omp_shared_destroy(x_shared);
			//for each shared variable "x"
			for(ASTNode child : sharedList.children()){
				IdentifierNode c = ((IdentifierExpressionNode) child).getIdentifier();

				parForItems.add(destroy("shared", c.name() + "_shared"));
			}

			//$omp_team_destroy(team);
			parForItems.add(destroy(TEAM, TEAM));

			StatementNode parForBody;
			parForBody = nodeFactory.newCompoundStatementNode(source, parForItems);

			cfn = nodeFactory.newCivlForNode(source, true, (DeclarationListNode) initializerNode, 
					nodeFactory.newIdentifierExpressionNode(source, 
							nodeFactory.newIdentifierNode(source, "loop_domain")), parForBody, null);

			items.add(cfn);
			//nodeFactory.new
			
			// $omp_shared_destroy(x_gshared);
			//for each shared variable "x"
			for(ASTNode child : sharedList.children()){
				IdentifierNode c = ((IdentifierExpressionNode) child).getIdentifier();

				items.add(destroy("gshared", c.name() + "_gshared"));
			}
			
			//$omp_gteam_destroy(gteam);
			items.add(destroy("gteam", "gteam"));

			pragmaBody = nodeFactory.newCompoundStatementNode(source, items);
			
			int index = node.childIndex();
			ASTNode parent = node.parent();
			parent.setChild(index, pragmaBody);
			children = pragmaBody.children();
			
			for (ASTNode child : children) {
				replaceOMPPragmas(child, privateList, sharedList);
			}
		} else if (node instanceof CommonOmpForNode) { 
			ForLoopInitializerNode initializerNode;
			List<BlockItemNode> items;
			List<BlockItemNode> forItems;
			CompoundStatementNode pragmaBody;
			Iterable<ASTNode> children = node.children();
			items = new LinkedList<>();
			forItems = new LinkedList<>();

			VariableDeclarationNode loopDomain;
			loopDomain = nodeFactory.newVariableDeclarationNode(source,
					nodeFactory.newIdentifierNode(source, "loop_domain"), 
					nodeFactory.newDomainTypeNode(source));
			items.add(loopDomain);
			ExpressionNode ompArriveLoop = nodeFactory.newCastNode(source, nodeFactory.newDomainTypeNode(source, 
					nodeFactory.newIntegerConstantNode(source, "0")), 			nodeFactory.newFunctionCallNode(source, this.identifierExpression(source, 
							"$omp_arrive_loop"), Arrays.asList(this.identifierExpression(source, TEAM), 
									this.identifierExpression(source, "loop_domain")), null));

			
			VariableDeclarationNode myIters;
			myIters = nodeFactory.newVariableDeclarationNode(source,
					nodeFactory.newIdentifierNode(source, "my_iters"), 
					nodeFactory.newDomainTypeNode(source, 
							nodeFactory.newIntegerConstantNode(source, "1")), ompArriveLoop);
			items.add(myIters);
			
			CivlForNode cfn;
			
			// for loop;
			initializerNode = nodeFactory
					.newForLoopInitializerNode(source,
							Arrays.asList(nodeFactory.newVariableDeclarationNode(
									source, nodeFactory.newIdentifierNode(source,
											"i"), nodeFactory.newBasicTypeNode(
													source, BasicTypeKind.INT))));

			int i = 0;
			for(ASTNode child : children) {
				node.removeChild(i);
				forItems.add((BlockItemNode) child);
				i++;
			}

			StatementNode forBody;
			forBody = nodeFactory.newCompoundStatementNode(source, forItems);
			
			cfn = nodeFactory.newCivlForNode(source, true, (DeclarationListNode) initializerNode, nodeFactory.newIdentifierExpressionNode(source, 
							nodeFactory.newIdentifierNode(source, "my_iters")), forBody, null);
			
			items.add(cfn);
			
			//$barrier_and_flush(team);
			items.add(barrierAndFlush(TEAM));
			
			pragmaBody = nodeFactory.newCompoundStatementNode(source, items);
			children = pragmaBody.children();
			int index = node.childIndex();
			ASTNode parent = node.parent();
			parent.setChild(index, pragmaBody);

			for (ASTNode child : children) {
				replaceOMPPragmas(child, privateIDs, sharedIDs);
			}

		} else if (node instanceof OmpSyncNode){ 
			String syncKind = ((OmpSyncNode) node).ompSyncNodeKind().toString();
			CompoundStatementNode body;
			LinkedList<BlockItemNode> items = new LinkedList<>();
			if(syncKind.equals("MASTER")){
				List<ExpressionNode> operands = new ArrayList<ExpressionNode>();
				operands.add(nodeFactory.newIdentifierExpressionNode(source, nodeFactory.newIdentifierNode(source, "_tid")));
				operands.add(nodeFactory.newIntegerConstantNode(source, "0"));
				int i = 0;
				for(ASTNode child : node.children()) {
					node.removeChild(i);
					items.add((BlockItemNode) child);
					i++;
				}
				body = nodeFactory.newCompoundStatementNode(source, items);
				IfNode ifStatement = nodeFactory.newIfNode(source, 
						nodeFactory.newOperatorNode(source, Operator.EQUALS, operands), body);
				int index = node.childIndex();
				ASTNode parent = node.parent();
				parent.setChild(index, ifStatement);
			} else if (syncKind.equals("BARRIER")){
				ExpressionStatementNode barrierAndFlush = barrierAndFlush(TEAM);
				int index = node.childIndex();
				ASTNode parent = node.parent();
				parent.setChild(index, barrierAndFlush);
			}
		} else if (node instanceof CommonOmpWorkshareNode){ 
			Iterable<ASTNode> children = node.children();
			String workshareKind = ((CommonOmpWorkshareNode) node).ompWorkshareNodeKind().toString();
			CompoundStatementNode body;
			LinkedList<BlockItemNode> items = new LinkedList<>();
			if(workshareKind.equals("SECTIONS")){
				int numberSections = 0;
				CompoundStatementNode pragmaBody = (CompoundStatementNode) node.child(7);
				ArrayList<LinkedList<BlockItemNode>> sectionsChildren = new ArrayList<LinkedList<BlockItemNode>>(); 
				for(ASTNode child : pragmaBody.children()){
					if(child instanceof CommonOmpWorkshareNode){
						if(((CommonOmpWorkshareNode) child).ompWorkshareNodeKind().toString().equals("SECTION")){
							LinkedList<BlockItemNode> sectionItems = new LinkedList<>();
							int i = 0;
							for(ASTNode sectionChild : child.children()) {
								child.removeChild(i);
								sectionItems.add((BlockItemNode) sectionChild);
								i++;
							}
							sectionsChildren.add(sectionItems);
							numberSections++;
						}
					}
				}
				
				ExpressionNode ompArriveSections = nodeFactory.newFunctionCallNode(source, this.identifierExpression(source, 
								"$omp_arrive_sections"), Arrays.asList(this.identifierExpression(source, TEAM), 
										this.identifierExpression(source, String.valueOf(numberSections))), null);
				
				VariableDeclarationNode my_secs;
				my_secs = nodeFactory.newVariableDeclarationNode(source,
						nodeFactory.newIdentifierNode(source, "my_secs"), 
						nodeFactory.newDomainTypeNode(source, 
								nodeFactory.newIntegerConstantNode(source, "1")), ompArriveSections);
				items.add(my_secs);
				
				CivlForNode cfn;
				
				List<BlockItemNode> forItems = new LinkedList<>();
				
				// for loop;
				ForLoopInitializerNode initializerNode = nodeFactory
						.newForLoopInitializerNode(source,
								Arrays.asList(nodeFactory.newVariableDeclarationNode(
										source, nodeFactory.newIdentifierNode(source,
												"i"), nodeFactory.newBasicTypeNode(
														source, BasicTypeKind.INT))));
				
				StatementNode forBody;
				StatementNode switchBody;
				List<BlockItemNode> switchItems = new LinkedList<>();
				int caseNumber = 0;
				for(LinkedList<BlockItemNode> tempChildren : sectionsChildren){
					StatementNode caseBody;
					List<BlockItemNode> caseItems = tempChildren;
					caseItems.add(nodeFactory.newBreakNode(source));
					caseBody = nodeFactory.newCompoundStatementNode(source, caseItems);
					SwitchLabelNode labelDecl = nodeFactory.newCaseLabelDeclarationNode(source, nodeFactory.newIntegerConstantNode(source, String.valueOf(caseNumber)), caseBody);
					switchItems.add(nodeFactory.newLabeledStatementNode(source, labelDecl, caseBody));
					System.out.println("HERE");
				}
				switchBody = nodeFactory.newCompoundStatementNode(source, switchItems);
				forItems.add(nodeFactory.newSwitchNode(source, this.identifierExpression(source, "i"), switchBody));
				forBody = nodeFactory.newCompoundStatementNode(source, forItems);
				
				cfn = nodeFactory.newCivlForNode(source, true, (DeclarationListNode) initializerNode, nodeFactory.newIdentifierExpressionNode(source, 
								nodeFactory.newIdentifierNode(source, "my_secs")), forBody, null);
				items.add(cfn);
				
				items.add(barrierAndFlush(TEAM));
				
				CompoundStatementNode sectionBody = nodeFactory.newCompoundStatementNode(source, items);
				
				int index = node.childIndex();
				ASTNode parent = node.parent();
				parent.setChild(index, sectionBody);

				for (ASTNode child : children) {
					replaceOMPPragmas(child, privateIDs, sharedIDs);
				}
				
				
			}
			if(workshareKind.equals("SINGLE")){
				
				ExpressionNode arriveSingle = nodeFactory.newFunctionCallNode(
						source,
						this.identifierExpression(source, "$omp_arrive_single"),
						Arrays.asList(this.identifierExpression(source, TEAM)), null);
				 items.add(nodeFactory.newVariableDeclarationNode(source,
						nodeFactory.newIdentifierNode(source, "owner"), 
						nodeFactory.newBasicTypeNode(source, BasicTypeKind.INT),
						arriveSingle));
				 
					List<ExpressionNode> operands = new ArrayList<ExpressionNode>();
					operands.add(this.identifierExpression(source, "owner"));
					operands.add(this.identifierExpression(source, "_tid"));
					int i = 0;
					CompoundStatementNode ifBody;
					LinkedList<BlockItemNode> ifItems = new LinkedList<>();
					for(ASTNode child : node.children()) {
						node.removeChild(i);
						ifItems.add((BlockItemNode) child);
						i++;
					}
					ifBody = nodeFactory.newCompoundStatementNode(source, ifItems);
					
					IfNode ifStatement = nodeFactory.newIfNode(source, 
							nodeFactory.newOperatorNode(source, Operator.EQUALS, operands), ifBody);
					items.add(ifStatement);
					items.add(barrierAndFlush(TEAM));
					body = nodeFactory.newCompoundStatementNode(source, items);
				 
					int index = node.childIndex();
					ASTNode parent = node.parent();
					parent.setChild(index, body);

					for (ASTNode child : children) {
						replaceOMPPragmas(child, privateIDs, sharedIDs);
					}
				
				
			}
		} else if(node instanceof IdentifierNode){
			if(privateIDs != null){
				for(ASTNode child : privateIDs.children()){
					IdentifierNode c = ((IdentifierExpressionNode) child).getIdentifier();
					if(c.name().equals(((IdentifierNode) node).name())){
						((IdentifierNode) node).setName("_" + ((IdentifierNode) node).name());
					}
				}
			}
			if(sharedIDs != null && ((IdentifierNode) node).getEntity() != null){
				for(ASTNode child : sharedIDs.children()){
					IdentifierNode c = ((IdentifierExpressionNode) child).getIdentifier();
					if(c.name().equals(((IdentifierNode) node).name())){
						ASTNode parent = getParentOfID((IdentifierNode) node);
						CompoundStatementNode readBody = sharedRead((IdentifierNode) node, (StatementNode) parent);
						int index = parent.childIndex();
						ASTNode parentNode = parent.parent();
						parentNode.setChild(index, readBody);
					}
				}
			}
			
		} else if(node instanceof ExpressionStatementNode && sharedIDs != null && node.child(0) instanceof OperatorNode && ((OperatorNode)node.child(0)).getOperator().toString().equals("ASSIGN")){			
			containsSharedWrite((OperatorNode) node.child(0), sharedIDs, 0, new ArrayList<String>());
			replaceOMPPragmas(node.child(0).child(1), privateIDs, sharedIDs);

		} else if(node != null){
			Iterable<ASTNode> children = node.children();
			for (ASTNode child : children) {
				replaceOMPPragmas(child, privateIDs, sharedIDs);
			}
		}

	}
	
	private ASTNode getParentOfID(IdentifierNode node){
		ASTNode parent = node.parent();
		while(!(parent instanceof StatementNode)){
			parent = parent.parent();
		}
		return parent;
	}
	
	private CompoundStatementNode sharedRead(IdentifierNode node, StatementNode parentStatement){
		List<BlockItemNode> items = new LinkedList<>();
		CompoundStatementNode bodyRead;
		
		VariableDeclarationNode temp;
		Type currentType = node.getEntity().getType();
		int nodesDeep = 0;
		while(currentType instanceof ArrayType){
			currentType = ((ArrayType) currentType).getElementType();
			nodesDeep++;
		}
		
		TypeNode tempType = ((VariableDeclarationNode) node.getEntity().getFirstDeclaration()).getTypeNode().copy();
		IdentifierNode tempID = nodeFactory.newIdentifierNode(source, "tmp");
		temp = nodeFactory.newVariableDeclarationNode(source, tempID, tempType);
		
		items.add(temp);
		if(nodesDeep == 0){
			items.add(read(node.name(), node.name()));
		} else {
			ASTNode parent = node.parent();
			StringBuilder k = new StringBuilder();
			k.append(node.name());
			while(nodesDeep > 0){
				parent = parent.parent();
				if(parent instanceof OperatorNode){
					OperatorNode on = (OperatorNode)parent;
					k.append("[" + ((IntegerConstantNode) on.child(1)).getStringRepresentation() + "]");
				}
				nodesDeep--;
			}
			items.add(read(k.toString(), node.name()));
		}
		node.setName("tmp");
		
		StatementNode copy = parentStatement.copy();
		items.add(copy);
		
		bodyRead = nodeFactory.newCompoundStatementNode(source, items);
		return bodyRead;
	}
	
	
	
	
	private void containsSharedWrite(OperatorNode node, SequenceNode<IdentifierExpressionNode> sharedIDs, int nodesDeep, ArrayList<String> arrayIndices){
		IdentifierExpressionNode origNode = null;
		if(node.child(0) instanceof IdentifierExpressionNode){
			origNode = (IdentifierExpressionNode) node.child(0);
			
			for(ASTNode child : sharedIDs.children()){
				IdentifierNode c = ((IdentifierExpressionNode) child).getIdentifier();
				if(c.name().equals(((CommonIdentifierNode) origNode.child(0)).name())){
					//Translate write access
					IdentifierNode in = (IdentifierNode) node.child(0).child(0);
					VariableDeclarationNode temp = null;
					Type currentType = in.getEntity().getType();
					while(currentType instanceof ArrayType){
						currentType = ((ArrayType) currentType).getElementType();
					}
					BasicTypeKind baseTypeKind = ((StandardBasicType) currentType).getBasicTypeKind();
					
					ExpressionNode initializer = (ExpressionNode) node.child(1).copy();
					if(!(in.getEntity().getType() instanceof ArrayType)){
						temp = (VariableDeclarationNode) in.getEntity().getDefinition().copy();
						temp.getIdentifier().setName("tmp");
						temp.setInitializer(initializer);
					} else{
						temp = nodeFactory.newVariableDeclarationNode(source, nodeFactory.newIdentifierNode(source, "tmp"), nodeFactory.newBasicTypeNode(source, baseTypeKind), initializer);
					}

					List<BlockItemNode> items = new LinkedList<>();;
					CompoundStatementNode bodyWrite;
					items.add(temp);

					if(nodesDeep == 0){
						items.add(write(c.name(), c.name()));
					} else {
						StringBuilder k = new StringBuilder();
						k.append(c.name());
						int j = 0;
						while(j < (nodesDeep - 1)){
							k.append("[" + arrayIndices.get(j) + "]");
							j++;
						}
						items.add(write(k.toString(), c.name()));
					}
					
					bodyWrite = nodeFactory.newCompoundStatementNode(source, items);
					ASTNode expNode = node.parent();
					for(int i=0; i < nodesDeep; i++){
						expNode = expNode.parent();
					}
					int index = expNode.childIndex();
					ASTNode parent = expNode.parent();
					parent.setChild(index, bodyWrite);
				}
			}
		} else if(node.child(0) instanceof OperatorNode) {
			if(((OperatorNode)node.child(0)).getOperator().toString().equals("SUBSCRIPT")){
				OperatorNode array = (OperatorNode) node.child(0);
				arrayIndices.add(((IntegerConstantNode) array.child(1)).getStringRepresentation());
			}
			containsSharedWrite((OperatorNode) node.child(0), sharedIDs, nodesDeep + 1, arrayIndices);
		}
	}

	private Triple<List<ASTNode>, List<ASTNode>, List<VariableDeclarationNode>> program(
			SequenceNode<ASTNode> root) {
		List<ASTNode> includedNodes = new ArrayList<>();
		List<VariableDeclarationNode> vars = new ArrayList<>();
		List<ASTNode> items;
		int number;
		items = new LinkedList<>();
		number = root.numChildren();
		for (int i = 0; i < number; i++) {
			ASTNode child = root.child(i);
			String sourceFile = child.getSource().getFirstToken()
					.getSourceFile().getName();

			root.removeChild(i);
			if (sourceFile.equals("omp.cvl")) {
				includedNodes.add(child);
			} else if (sourceFile.equals("stdio.cvl")) {
				includedNodes.add(child);
			} else if (sourceFile.endsWith(".h")) {
				if (child.nodeKind() == NodeKind.VARIABLE_DECLARATION) {
					VariableDeclarationNode variableDeclaration = (VariableDeclarationNode) child;
					if (sourceFile.equals("stdio.h")) {
						// keep variable declaration nodes from stdio, i.e.,
						// stdout, stdin, etc.
						items.add(variableDeclaration);
					} 
				} else {
					includedNodes.add(child);
				}
			} else {
				if (child.nodeKind() == NodeKind.VARIABLE_DECLARATION) {
					VariableDeclarationNode variable = (VariableDeclarationNode) child;

					if (variable.getTypeNode().isInputQualified()
							|| variable.getTypeNode().isOutputQualified()) {
						vars.add(variable);
						continue;
					}
				}
				items.add((BlockItemNode) child);
			}
		}
		return new Triple<>(items, includedNodes, vars);
	}
}
