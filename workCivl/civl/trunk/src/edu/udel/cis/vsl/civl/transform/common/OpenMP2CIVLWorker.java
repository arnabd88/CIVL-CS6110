package edu.udel.cis.vsl.civl.transform.common;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.NoSuchElementException;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.entity.IF.Entity;
import edu.udel.cis.vsl.abc.ast.entity.IF.Variable;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode.NodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.NodePredicate;
import edu.udel.cis.vsl.abc.ast.node.IF.PairNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.compound.CompoundInitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.compound.DesignationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.DeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FieldDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.InitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.TypedefDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.CompoundLiteralNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IntegerConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.label.SwitchLabelNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpDeclarativeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpExecutableNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpForNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpParallelNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpReductionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpSymbolReductionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpSyncNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpWorksharingNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.AtomicNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CivlForNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CompoundStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.DeclarationListNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ExpressionStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ForLoopInitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ForLoopNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.IfNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.LoopNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.ArrayTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.FunctionTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.PointerTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.StructureOrUnionTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypedefNameNode;
import edu.udel.cis.vsl.abc.ast.type.IF.ArrayType;
import edu.udel.cis.vsl.abc.ast.type.IF.Field;
import edu.udel.cis.vsl.abc.ast.type.IF.PointerType;
import edu.udel.cis.vsl.abc.ast.type.IF.QualifiedObjectType;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.StructureOrUnionType;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.front.IF.CivlcTokenConstant;
import edu.udel.cis.vsl.abc.front.c.parse.COmpParser;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SourceFile;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.model.IF.CIVLSyntaxException;
import edu.udel.cis.vsl.civl.transform.IF.OpenMP2CIVLTransformer;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.civl.util.IF.Triple;

public class OpenMP2CIVLWorker extends BaseWorker {

	/* ************************** Private Static Fields ********************** */

	private static String OMP_SET_LOCK = "omp_set_lock";

	private static String OMP_UNSET_LOCK = "omp_unset_lock";

	private static String OMPPRE = "_omp_";

	/**
	 * The name of the identifier of the $omp_gteam variable in the final CIVL
	 * program.
	 */
	private static String GTEAM = "_omp_gteam";

	/**
	 * The name of the identifier of the $omp_team variable in the final CIVL
	 * program.
	 */
	private static String TEAM = "_omp_team";

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
	private static String NTHREADS = "_omp_nthreads";

	/**
	 * The name of the input variable denoting the number of OpenMP threads in
	 * the final CIVL-C program.
	 */
	private static String THREADMAX = "_omp_thread_max";

	/**
	 * The name of the variable denoting the thread number in the CIVL_C
	 * program.
	 */
	private static String TID = "_omp_tid";

	/* **************************** Instance Fields ************************* */

	/**
	 * * There are new nodes created by the transformer, other than parsing from
	 * some source file. All new nodes share the same source.
	 */
	@SuppressWarnings("unused")
	private Source source;

	/**
	 * Variable that is increment for naming of temp variables that are created
	 */
	private int tmpCount = 0;

	private int tempWriteCount = 0;

	/**
	 * Counter for locating $omp_arrive_loop functions
	 */
	private int ompArriveLoopCounter = 0;

	/**
	 * Counter for locating $omp_arrive_sections functions
	 */
	private int ompArriveSections = 0;

	/**
	 * Counter for locating $omp_arrive_single functions
	 */
	private int ompArriveSingle = 0;

	/**
	 * If the same variable is replaced in the same expression then use the temp
	 * name of the first one
	 */
	private ArrayList<Triple<String, StatementNode, String>> sharedReplaced = new ArrayList<Triple<String, StatementNode, String>>();

	SequenceNode<BlockItemNode> root;

	/**
	 * For each critical section encountered, create a new critical variable
	 */
	private ArrayList<String> criticalNames = new ArrayList<String>();
	private HashMap<ASTNode, ArrayList<Pair<VariableDeclarationNode, ExpressionStatementNode>>> sharedRead = new HashMap<ASTNode, ArrayList<Pair<VariableDeclarationNode, ExpressionStatementNode>>>();
	private HashMap<ASTNode, ArrayList<Pair<VariableDeclarationNode, ExpressionStatementNode>>> sharedWrite = new HashMap<ASTNode, ArrayList<Pair<VariableDeclarationNode, ExpressionStatementNode>>>();
	private ArrayList<TypedefDeclarationNode> structsDefsToAdd = new ArrayList<TypedefDeclarationNode>();
	private ArrayList<StructureOrUnionTypeNode> structsToAdd = new ArrayList<StructureOrUnionTypeNode>();
	private ArrayList<Triple<BlockItemNode, IdentifierNode, String>> tempVars = new ArrayList<Triple<BlockItemNode, IdentifierNode, String>>();

	private int lastLoopVar = -1;

	/**
	 * The command line configuration information.
	 */
	private CIVLConfiguration config;

	/* ****************************** Constructor ************************** */
	/**
	 * Creates a new instance of OpenMP2CIVLTransformer.
	 * 
	 * @param astFactory
	 *            The ASTFactory that will be used to create new nodes.
	 */
	public OpenMP2CIVLWorker(ASTFactory astFactory, CIVLConfiguration config) {
		super(OpenMP2CIVLTransformer.LONG_NAME, astFactory);
		this.identifierPrefix = "$omp_";
		this.config = config;
	}

	/* *************************** Private Methods ************************* */

	private void processOmpLockCalls(ASTNode node) {
		for (ASTNode child : node.children()) {
			if (child == null)
				continue;
			if (child instanceof FunctionCallNode) {
				FunctionCallNode funcCall = (FunctionCallNode) child;
				if (funcCall.getFunction() instanceof IdentifierExpressionNode) {
					SequenceNode<ExpressionNode> newArgs;
					IdentifierNode name = ((IdentifierExpressionNode) funcCall
							.getFunction()).getIdentifier();

					if (name.name().equals(OMP_SET_LOCK)
							|| name.name().equals(OMP_UNSET_LOCK)) {
						ExpressionNode oldArg = funcCall.getArgument(0);

						name.setName("$" + name.name());
						oldArg.parent().removeChild(oldArg.childIndex());
						newArgs = nodeFactory.newSequenceNode(this.newSource(
								"actual parameter list of " + name,
								CivlcTokenConstant.ARGUMENT_LIST),
								"Actual parameters", Arrays.asList(oldArg, this
										.identifierExpression(this.newSource(
												TEAM,
												CivlcTokenConstant.IDENTIFIER),
												TEAM)));
						funcCall.setArguments(newArgs);
					}

				}

			}
			processOmpLockCalls(child);
		}
	}

	/**
	 * Creates the declaration node for the input variable
	 * <code>_omp_thread_max</code>.
	 * 
	 * @param range
	 *            a source object specifying a specific range in the original
	 *            source into which the new declaration is going to be inserted;
	 *            the line numbers of this range will be included in output to
	 *            give an idea of the location into which the generated text was
	 *            inserted. It is probably somewhere near the beginning of the
	 *            file.
	 * 
	 * @return The declaration node of the input variable
	 *         <code>_omp_thread_max</code>.
	 */
	private VariableDeclarationNode threadMaxDeclaration() {
		final String place = "threadMaxDeclaration";
		TypeNode nthreadsType = nodeFactory.newBasicTypeNode(
				newSource(place, CivlcTokenConstant.INT), BasicTypeKind.INT);
		IdentifierNode identifierNode = nodeFactory.newIdentifierNode(
				newSource(place, CivlcTokenConstant.IDENTIFIER), THREADMAX);

		nthreadsType.setInputQualified(true);
		return nodeFactory.newVariableDeclarationNode(
				newSource(place, CivlcTokenConstant.DECLARATION),
				identifierNode, nthreadsType);
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
		final String place = "gteamDeclaration";
		gteamType = nodeFactory.newTypedefNameNode(
				nodeFactory.newIdentifierNode(
						newSource(place, CivlcTokenConstant.TYPE), GTEAM_TYPE),
				null);
		gteamCreate = nodeFactory.newFunctionCallNode(
				newSource(place, CivlcTokenConstant.CALL),
				this.identifierExpression(
						newSource(place, CivlcTokenConstant.IDENTIFIER),
						GTEAM_CREATE), Arrays.asList(
						nodeFactory.newHereNode(newSource(place,
								CivlcTokenConstant.HERE)), this
								.identifierExpression(
										newSource(place,
												CivlcTokenConstant.IDENTIFIER),
										NTHREADS)), null);
		return nodeFactory
				.newVariableDeclarationNode(
						newSource(place, CivlcTokenConstant.DECLARATION),
						nodeFactory
								.newIdentifierNode(
										newSource(place,
												CivlcTokenConstant.IDENTIFIER),
										GTEAM), gteamType, gteamCreate);
	}

	/**
	 * Creates the declaration node for the variable <code>team</code> , which
	 * is of <code>$omp_team</code> type and has an initializer to call
	 * <code>$omp_team_create()</code>. That is:
	 * <code>$omp_team team = $omp_team_create($here, gteam, _tid)</code> .
	 * 
	 * @return The declaration node of the variable <code>team</code>.
	 */
	private VariableDeclarationNode teamDeclaration() {
		TypeNode teamType;
		ExpressionNode teamCreate;
		final String place = "teamDelcaration";

		teamType = nodeFactory.newTypedefNameNode(
				nodeFactory.newIdentifierNode(
						newSource(place, CivlcTokenConstant.TYPE), TEAM_TYPE),
				null);
		teamCreate = nodeFactory.newFunctionCallNode(
				newSource(place, CivlcTokenConstant.CALL),
				this.identifierExpression(
						newSource(place, CivlcTokenConstant.IDENTIFIER),
						TEAM_CREATE), Arrays.asList(
						nodeFactory.newHereNode(newSource(place,
								CivlcTokenConstant.HERE)), this
								.identifierExpression(
										newSource(place,
												CivlcTokenConstant.IDENTIFIER),
										GTEAM), this
								.identifierExpression(
										newSource(place,
												CivlcTokenConstant.IDENTIFIER),
										TID)), null);
		return nodeFactory.newVariableDeclarationNode(
				newSource(place, CivlcTokenConstant.DECLARATION),
				nodeFactory.newIdentifierNode(
						newSource(place, CivlcTokenConstant.IDENTIFIER), TEAM),
				teamType, teamCreate);
	}

	/**
	 * Creates the declaration node for the variable <code>gshared</code>, which
	 * is of <code>$omp_gshared</code> type and has an initializer to call
	 * <code>$omp_gshared_create()</code>. That is: <code>$omp_gshared 
	 * x_gshared = $omp_gshared_create($omp_gteam, void *original)</code> .
	 * 
	 * @return The declaration node of the variable <code>x_gshared</code>.
	 */
	private VariableDeclarationNode gsharedDeclaration(IdentifierNode variable) {
		TypeNode gsharedType;
		ExpressionNode gsharedCreate;
		final String place = variable + "_gsharedDeclaration";

		TypeNode currentType = ((VariableDeclarationNode) ((Variable) variable
				.getEntity()).getFirstDeclaration()).getTypeNode().copy();

		ExpressionNode addressOf = nodeFactory.newOperatorNode(
				newSource(place, CivlcTokenConstant.AMPERSAND),
				Operator.ADDRESSOF, Arrays.asList(this.identifierExpression(
						newSource(place, CivlcTokenConstant.IDENTIFIER),
						variable.name())));

		gsharedType = nodeFactory.newTypedefNameNode(nodeFactory
				.newIdentifierNode(newSource(place, CivlcTokenConstant.TYPE),
						GSHARED_TYPE), null);

		if (currentType.isRestrictQualified() || currentType.isInputQualified()
				|| currentType.isVolatileQualified()) {
			addressOf = nodeFactory.newCastNode(
					newSource(place, CivlcTokenConstant.CAST), nodeFactory
							.newPointerTypeNode(
									newSource(place, CivlcTokenConstant.TYPE),
									nodeFactory.newVoidTypeNode(newSource(
											place, CivlcTokenConstant.VOID))),
					addressOf);
		}

		gsharedCreate = nodeFactory
				.newFunctionCallNode(
						newSource(place, CivlcTokenConstant.CALL),
						this.identifierExpression(
								newSource(place, CivlcTokenConstant.IDENTIFIER),
								GSHARED_CREATE), Arrays.asList(this
								.identifierExpression(
										newSource(place,
												CivlcTokenConstant.IDENTIFIER),
										GTEAM), addressOf), null);
		return nodeFactory.newVariableDeclarationNode(
				newSource(place, CivlcTokenConstant.DECLARATION),
				nodeFactory.newIdentifierNode(
						newSource(place, CivlcTokenConstant.IDENTIFIER), OMPPRE
								+ variable.name() + "_gshared"), gsharedType,
				gsharedCreate);
	}

	/**
	 * Creates the declaration node for the variable <code>shared</code>, which
	 * is of <code>$omp_shared</code> type and has an initializer to call
	 * <code>$omp_shared_create()</code>. That is: <code>$omp_shared 
	 * x_shared = $omp_shared_create($omp_team team, $omp_gshared gshared, 
	 * void *local, void *status)</code> .
	 * 
	 * @return The declaration node of the variable <code>x_shared</code>.
	 */
	private VariableDeclarationNode sharedDeclaration(IdentifierNode variable) {
		TypeNode sharedType;
		ExpressionNode sharedCreate;
		final String place = variable + "_sharedDeclaration";

		TypeNode currentType = ((VariableDeclarationNode) ((Variable) variable
				.getEntity()).getFirstDeclaration()).getTypeNode().copy();

		sharedType = nodeFactory
				.newTypedefNameNode(
						nodeFactory.newIdentifierNode(
								newSource(place, CivlcTokenConstant.TYPE),
								SHARED_TYPE), null);
		ExpressionNode addressOfLocalVar = nodeFactory.newOperatorNode(
				newSource(place, CivlcTokenConstant.AMPERSAND),
				Operator.ADDRESSOF,
				Arrays.asList(this.identifierExpression(
						newSource(place, CivlcTokenConstant.IDENTIFIER), OMPPRE
								+ variable.name() + "_local")));
		ExpressionNode addressOfStatusVar = nodeFactory.newOperatorNode(
				newSource(place, CivlcTokenConstant.AMPERSAND),
				Operator.ADDRESSOF,
				Arrays.asList(this.identifierExpression(
						newSource(place, CivlcTokenConstant.IDENTIFIER), OMPPRE
								+ variable.name() + "_status")));

		if (currentType.isRestrictQualified()
				|| currentType.isVolatileQualified()) {
			addressOfLocalVar = nodeFactory.newCastNode(
					newSource(place, CivlcTokenConstant.CAST), nodeFactory
							.newPointerTypeNode(
									newSource(place, CivlcTokenConstant.TYPE),
									nodeFactory.newVoidTypeNode(newSource(
											place, CivlcTokenConstant.VOID))),
					addressOfLocalVar);
		}

		sharedCreate = nodeFactory
				.newFunctionCallNode(
						newSource(place, CivlcTokenConstant.CALL),
						this.identifierExpression(
								newSource(place, CivlcTokenConstant.IDENTIFIER),
								SHARED_CREATE), Arrays.asList(this
								.identifierExpression(
										newSource(place,
												CivlcTokenConstant.IDENTIFIER),
										TEAM), this
								.identifierExpression(
										newSource(place,
												CivlcTokenConstant.IDENTIFIER),
										OMPPRE + variable.name() + "_gshared"),
								addressOfLocalVar, addressOfStatusVar), null);

		return nodeFactory.newVariableDeclarationNode(
				newSource(place, CivlcTokenConstant.DECLARATION),
				nodeFactory.newIdentifierNode(
						newSource(place, CivlcTokenConstant.IDENTIFIER), OMPPRE
								+ variable.name() + "_shared"), sharedType,
				sharedCreate);
	}

	/**
	 * Creates the function call node for <code>destroy</code>, which is of void
	 * type. That is: <code>$omp_(g)team_destroy($omp_(g)team (g)team)
	 * </code> . This can be used to destroy gteam or team depending in the type
	 * parameter
	 * 
	 * @return The function call node of <code>$omp_(g)team_destroy</code>.
	 */
	private ExpressionStatementNode destroy(String type, String object) {
		final String place = "destroyCall";
		ExpressionNode function = this.identifierExpression(
				newSource(place, CivlcTokenConstant.IDENTIFIER), "$omp_" + type
						+ "_destroy");

		return nodeFactory.newExpressionStatementNode(nodeFactory
				.newFunctionCallNode(newSource(place, CivlcTokenConstant.CALL),
						function, Arrays.asList(this
								.identifierExpression(
										newSource(place,
												CivlcTokenConstant.IDENTIFIER),
										object)), null));
	}

	/**
	 * Creates the function call node for <code>barrier_and_flush</code>, which
	 * is of void type. That is:
	 * <code>$omp_barrier_and_flush($omp_team team) </code> . This is used as a
	 * barrier and a flush on all shared objects owned by the team
	 * 
	 * @return The function call node of <code>$omp_barrier_and_flush</code>.
	 */
	private ExpressionStatementNode barrierAndFlush(String object) {
		final String place = "barrierAndFlushCall";
		ExpressionNode function = this.identifierExpression(
				newSource(place, CivlcTokenConstant.IDENTIFIER),
				"$omp_barrier_and_flush");

		return nodeFactory.newExpressionStatementNode(nodeFactory
				.newFunctionCallNode(newSource(place, CivlcTokenConstant.CALL),
						function, Arrays.asList(this
								.identifierExpression(
										newSource(place,
												CivlcTokenConstant.IDENTIFIER),
										object)), null));
	}

	/**
	 * Creates the function call node for <code>write</code>, which is of void
	 * type. That is: <code> $omp_write($omp_shared shared, 
	 * void *ref, void *value)</code> . This is used to write to shared
	 * variables.
	 * 
	 * @return The function call node of <code>$omp_write</code>.
	 */
	private ExpressionStatementNode write(ExpressionNode variable,
			String sharedName, ExpressionNode writeName, Type origType) {
		final String place = sharedName + "_sharedWriteCall";
		ExpressionNode function = this.identifierExpression(
				newSource(place, CivlcTokenConstant.IDENTIFIER), "$omp_write");
		ExpressionNode addressOfVar = nodeFactory.newOperatorNode(
				newSource(place, CivlcTokenConstant.AMPERSAND),
				Operator.ADDRESSOF, Arrays.asList(variable));

		if (origType instanceof QualifiedObjectType
				&& ((QualifiedObjectType) origType).isVolatileQualified()) {
			addressOfVar = nodeFactory.newCastNode(
					newSource(place, CivlcTokenConstant.CAST), nodeFactory
							.newPointerTypeNode(
									newSource(place, CivlcTokenConstant.TYPE),
									nodeFactory.newVoidTypeNode(newSource(
											place, CivlcTokenConstant.VOID))),
					addressOfVar);
		}

		ExpressionNode addressOfTmp = nodeFactory.newOperatorNode(
				newSource(place, CivlcTokenConstant.AMPERSAND),
				Operator.ADDRESSOF, Arrays.asList(writeName));
		return nodeFactory.newExpressionStatementNode(nodeFactory
				.newFunctionCallNode(newSource(place, CivlcTokenConstant.CALL),
						function, Arrays.asList(this
								.identifierExpression(
										newSource(place,
												CivlcTokenConstant.IDENTIFIER),
										OMPPRE + sharedName + "_shared"),
								addressOfVar, addressOfTmp), null));
	}

	/**
	 * Creates the function call node for <code>read</code>, which is of void
	 * type. That is: <code> $omp_read($omp_shared shared, 
	 * void *result, void *ref)</code> . This is used to read shared variables.
	 * 
	 * @return The function call node of <code>$omp_read</code>.
	 */
	private ExpressionStatementNode read(ExpressionNode parent,
			String sharedName, String tmpName, Type origType) {
		final String place = sharedName + "_sharedReadCall";
		ExpressionNode function = this.identifierExpression(
				newSource(place, CivlcTokenConstant.IDENTIFIER), "$omp_read");

		ExpressionNode addressOfVar = nodeFactory.newOperatorNode(
				newSource(place, CivlcTokenConstant.AMPERSAND),
				Operator.ADDRESSOF, Arrays.asList(parent));

		if (origType instanceof QualifiedObjectType
				&& ((QualifiedObjectType) origType).isVolatileQualified()) {
			addressOfVar = nodeFactory.newCastNode(
					newSource(place, CivlcTokenConstant.CAST), nodeFactory
							.newPointerTypeNode(
									newSource(place, CivlcTokenConstant.TYPE),
									nodeFactory.newVoidTypeNode(newSource(
											place, CivlcTokenConstant.VOID))),
					addressOfVar);
		}

		ExpressionNode addressOfTmp = nodeFactory.newOperatorNode(
				newSource(place, CivlcTokenConstant.AMPERSAND),
				Operator.ADDRESSOF, Arrays.asList(this.identifierExpression(
						newSource(place, CivlcTokenConstant.IDENTIFIER),
						tmpName)));
		return nodeFactory.newExpressionStatementNode(nodeFactory
				.newFunctionCallNode(newSource(place, CivlcTokenConstant.CALL),
						function, Arrays.asList(this
								.identifierExpression(
										newSource(place,
												CivlcTokenConstant.IDENTIFIER),
										OMPPRE + sharedName + "_shared"),
								addressOfTmp, addressOfVar), null));
	}

	/**
	 * Creates the function call node for <code>apply_assoc</code>, which is of
	 * void type. That is: <code> $omp_apply_assoc($omp_shared shared, 
	 *  $operation op, void *local)</code> . This is used to apply associated
	 * operators.
	 * 
	 * @return The function call node of <code>$omp_apply_assoc</code>.
	 * @throws SyntaxException
	 */
	private ExpressionStatementNode applyAssoc(String variable, String operation)
			throws SyntaxException {
		final String place = variable + "applyAssoc(" + operation + ")";
		ExpressionNode function = this.identifierExpression(
				newSource(place, CivlcTokenConstant.IDENTIFIER),
				"$omp_apply_assoc");
		ExpressionNode addressOfVar = nodeFactory.newOperatorNode(
				newSource(place, CivlcTokenConstant.AMPERSAND),
				Operator.ADDRESSOF,
				Arrays.asList(this.identifierExpression(
						newSource(place, CivlcTokenConstant.IDENTIFIER), OMPPRE
								+ variable + "_reduction")));
		if (operation.equals("PLUSEQ")) {
			operation = "CIVL_SUM";
			// op = nodeFactory.newIntegerConstantNode(source, representation)
		}

		return nodeFactory
				.newExpressionStatementNode(nodeFactory.newFunctionCallNode(
						newSource(place, CivlcTokenConstant.CALL),
						function,
						Arrays.asList(
								this.identifierExpression(
										newSource(place,
												CivlcTokenConstant.IDENTIFIER),
										OMPPRE + variable + "_shared"),
								nodeFactory
										.newIntegerConstantNode(
												newSource(
														place,
														CivlcTokenConstant.INTEGER_CONSTANT),
												"3"), addressOfVar), null));
	}

	/* ********************* Methods From TransformerWorker ****************** */

	/**
	 * Transform an AST of a OpenMP program in C into an equivalent AST of
	 * CIVL-C program.<br>
	 * 
	 * @param ast
	 *            The AST of the original OpenMP program in C.
	 * @return An AST of CIVL-C program equivalent to the original OpenMP
	 *         program.
	 * @throws SyntaxException
	 */
	@Override
	public AST transform(AST ast) throws SyntaxException {
		root = ast.getRootNode();
		AST newAst;
		List<BlockItemNode> externalList;
		VariableDeclarationNode threadMax;
		SequenceNode<BlockItemNode> newRootNode;
		List<BlockItemNode> includedNodes = new ArrayList<>();
		List<VariableDeclarationNode> mainParameters = new ArrayList<>();
		int count;
		Triple<List<BlockItemNode>, List<BlockItemNode>, List<VariableDeclarationNode>> result;
		String criticalDeclaration = "criticalDeclarations";
		AST civlcAST = this.parseSystemLibrary("civlc.cvh");
		AST civlcOmpAST = this.parseSystemLibrary("civl-omp.cvh");

		assert this.astFactory == ast.getASTFactory();
		assert this.nodeFactory == astFactory.getNodeFactory();
		ast.release();

		// declaring $input int _omp_thread_max;
		threadMax = this.threadMaxDeclaration();

		SequenceNode<IdentifierExpressionNode> threadPrivateList;

		List<IdentifierExpressionNode> list = new LinkedList<IdentifierExpressionNode>();
		threadPrivateList = nodeFactory.newSequenceNode(
				newSource("threadList", CivlcTokenConstant.ARGUMENT_LIST),
				"threadPrivateList", list);

		// Recursive call to replace all omp code
		replaceOMPPragmas(root, null, null, null, null, threadPrivateList);

		// Add in statements for omp read and writes
		addStatements(sharedWrite, "write");
		addStatements(sharedRead, "read");

		// Eliminate extra barriers
		fix_duplicated_barrier_flush(root, false);

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
		// Add threadMax declaration
		externalList.add(threadMax);
		for (String name : criticalNames) {
			externalList.add(nodeFactory.newVariableDeclarationNode(
					newSource(criticalDeclaration,
							CivlcTokenConstant.DECLARATION), nodeFactory
							.newIdentifierNode(
									newSource(criticalDeclaration,
											CivlcTokenConstant.IDENTIFIER),
									name), nodeFactory.newBasicTypeNode(
							newSource(criticalDeclaration,
									CivlcTokenConstant.BOOL),
							BasicTypeKind.BOOL), nodeFactory
							.newBooleanConstantNode(
									newSource(criticalDeclaration,
											CivlcTokenConstant.FALSE), false)));
		}

		externalList.addAll(result.first);
		newRootNode = nodeFactory.newSequenceNode(null, "TranslationUnit",
				externalList);
		completeSources(newRootNode);
		this.processOmpLockCalls(newRootNode);
		newAst = astFactory.newAST(newRootNode, ast.getSourceFiles(),
				ast.isWholeProgram());
		boolean ompHeader = false;
		for (SourceFile sourceFile : ast.getSourceFiles()) {
			String filename = sourceFile.getName();

			if (filename.equals("omp.h")) {
				ompHeader = true;
			}
		}
		if (!ompHeader) {
			newAst = this.combineASTs(civlcOmpAST, newAst);
			newAst = this.combineASTs(civlcAST, newAst);
		}
		// newAst.prettyPrint(System.out, true);
		return newAst;
	}

	private void addStatements(
			HashMap<ASTNode, ArrayList<Pair<VariableDeclarationNode, ExpressionStatementNode>>> sharedMap,
			String readWrite) {
		for (ASTNode key : sharedMap.keySet()) {
			ArrayList<Pair<VariableDeclarationNode, ExpressionStatementNode>> statements = sharedMap
					.get(key);
			ASTNode parent = key.parent();
			if (parent instanceof ForLoopNode || parent instanceof IfNode) {
				createBody(key);
				parent = key.parent();
			}
			int index = key.childIndex();
			int i = 0;

			for (Pair<VariableDeclarationNode, ExpressionStatementNode> pair : statements) {
				if (pair.left != null) {
					insertChildAt(index + i, key.parent(), pair.left);
					i++;
				}
			}

			for (Pair<VariableDeclarationNode, ExpressionStatementNode> pair : statements) {
				if (pair.right != null) {
					if (readWrite.equals("write")) {
						insertChildAt(index + i + 1, key.parent(), pair.right);
					} else {
						insertChildAt(index + i, key.parent(), pair.right);

					}
					i++;
				}
			}
		}
	}

	/**
	 * Recursive method to replace all OpenMP pragmas and functions. The type of
	 * the node is checked and if it matches then the code is modified, deleted,
	 * or inserted to create a pure CIVL-C representation.
	 * 
	 * @param node
	 * @param privateIDs
	 * @param sharedIDs
	 * @param reductionIDs
	 * @param firstPrivateIDs
	 * @param threadPrivateIDs
	 * @throws SyntaxException
	 */
	@SuppressWarnings("unchecked")
	private void replaceOMPPragmas(ASTNode node,
			SequenceNode<IdentifierExpressionNode> privateIDs,
			SequenceNode<IdentifierExpressionNode> sharedIDs,
			SequenceNode<IdentifierExpressionNode> reductionIDs,
			SequenceNode<IdentifierExpressionNode> firstPrivateIDs,
			SequenceNode<IdentifierExpressionNode> threadPrivateIDs)
			throws SyntaxException {

		// Check if a pragma is nested inside a parallel. If not then remove
		// the pragma
		if (node instanceof OmpExecutableNode) {
			if (!(node instanceof OmpParallelNode)) {
				// check if node is nested in omp parallel node
				ASTNode parent = node.parent();
				boolean nested = false;
				while (parent != null) {
					parent = parent.parent();
					if (parent instanceof OmpParallelNode) {
						nested = true;
						break;
					}
					if (parent instanceof CivlForNode) {
						if (((CivlForNode) parent).isParallel()) {
							nested = true;
							break;
						}
					}
				}
				if (!nested) {
					if (node instanceof OmpSyncNode) {
						ASTNode body = node.child(7);
						body.remove();
						int index = node.childIndex();
						ASTNode directParent = node.parent();
						node.remove();
						directParent.setChild(index, body);
						return;
					}
				}
			}

		}
		// Check if the node is a parallel node
		if (node instanceof OmpParallelNode) {
			List<BlockItemNode> items;
			CompoundStatementNode pragmaBody;
			VariableDeclarationNode gteamVar;
			SequenceNode<IdentifierExpressionNode> sharedList;
			SequenceNode<IdentifierExpressionNode> privateList;
			SequenceNode<IdentifierExpressionNode> firstPrivateList;
			SequenceNode<IdentifierExpressionNode> reductionList = null;
			SequenceNode<OmpReductionNode> ompReductionNode;
			Iterable<ASTNode> children;
			String parallelNode = "parallelPragma";
			items = new LinkedList<>();
			children = node.children();

			// int _nthreads = 1+$choose_int(_omp_thread_max);
			String nthreadDeclaration = "_nthreadsDeclaration";
			VariableDeclarationNode nthreads;
			ExpressionNode add;
			ExpressionNode numThreads = ((OmpParallelNode) node).numThreads();

			removeNodeFromParent(numThreads);

			// If there is no num_threads clause for the parallel pragma then
			// get the number of threads from the CIVL input.
			if (numThreads == null) {
				numThreads = this.identifierExpression(
						newSource(nthreadDeclaration,
								CivlcTokenConstant.IDENTIFIER), OMPPRE
								+ "num_threads");
			}

			add = nodeFactory
					.newOperatorNode(
							newSource(nthreadDeclaration,
									CivlcTokenConstant.PLUS),
							Operator.PLUS,
							Arrays.asList(
									nodeFactory
											.newIntegerConstantNode(
													newSource(
															nthreadDeclaration,
															CivlcTokenConstant.INTEGER_CONSTANT),
													"1"),
									nodeFactory
											.newFunctionCallNode(
													newSource(
															nthreadDeclaration,
															CivlcTokenConstant.CHOOSE),
													this.identifierExpression(
															newSource(
																	nthreadDeclaration,
																	CivlcTokenConstant.IDENTIFIER),
															"$choose_int"),
													Arrays.asList(numThreads),
													null)));

			nthreads = nodeFactory.newVariableDeclarationNode(
					newSource(parallelNode, CivlcTokenConstant.DECLARATION),
					nodeFactory.newIdentifierNode(
							newSource(nthreadDeclaration,
									CivlcTokenConstant.IDENTIFIER), OMPPRE
									+ "nthreads"), nodeFactory
							.newBasicTypeNode(
									newSource(nthreadDeclaration,
											CivlcTokenConstant.INT),
									BasicTypeKind.INT), add);
			items.add(this.elaborateCallNode(numThreads.copy()));
			items.add(nthreads);

			// $range thread_range = 0 .. nthreads-1;
			String threadRangeDeclaration = "thread_rangeDeclaration";
			VariableDeclarationNode threadRange;
			threadRange = nodeFactory
					.newVariableDeclarationNode(
							newSource(parallelNode,
									CivlcTokenConstant.DECLARATION),
							nodeFactory.newIdentifierNode(
									newSource(threadRangeDeclaration,
											CivlcTokenConstant.IDENTIFIER),
									OMPPRE + "thread_range"),
							nodeFactory.newRangeTypeNode(newSource(
									threadRangeDeclaration,
									CivlcTokenConstant.RANGE)),
							nodeFactory
									.newRegularRangeNode(
											newSource(threadRangeDeclaration,
													CivlcTokenConstant.RANGE),
											nodeFactory
													.newIntegerConstantNode(
															newSource(
																	threadRangeDeclaration,
																	CivlcTokenConstant.INTEGER_CONSTANT),
															"0"),
											nodeFactory
													.newOperatorNode(
															newSource(
																	threadRangeDeclaration,
																	CivlcTokenConstant.SUB),
															Operator.MINUS,
															Arrays.asList(
																	this.identifierExpression(
																			newSource(
																					threadRangeDeclaration,
																					CivlcTokenConstant.IDENTIFIER),
																			OMPPRE
																					+ "nthreads"),
																	nodeFactory
																			.newIntegerConstantNode(
																					newSource(
																							threadRangeDeclaration,
																							CivlcTokenConstant.INTEGER_CONSTANT),
																					"1")))));
			items.add(threadRange);

			// $domain(1) dom = ($domain){thread_range};
			String domainDeclaration = "domainDeclaration";
			List<PairNode<DesignationNode, InitializerNode>> initList = new ArrayList<PairNode<DesignationNode, InitializerNode>>();
			initList.add(nodeFactory.newPairNode(
					newSource(domainDeclaration, CivlcTokenConstant.STRUCT),
					(DesignationNode) null, (InitializerNode) this
							.identifierExpression(
									newSource(domainDeclaration,
											CivlcTokenConstant.IDENTIFIER),
									OMPPRE + "thread_range")));
			CompoundInitializerNode temp = nodeFactory
					.newCompoundInitializerNode(
							newSource(domainDeclaration,
									CivlcTokenConstant.INITIALIZER_LIST),
							initList);
			CompoundLiteralNode cln = nodeFactory.newCompoundLiteralNode(
					newSource(domainDeclaration,
							CivlcTokenConstant.COMPOUND_LITERAL), nodeFactory
							.newDomainTypeNode(newSource(domainDeclaration,
									CivlcTokenConstant.DOMAIN)), temp);

			VariableDeclarationNode loopDomain;
			loopDomain = nodeFactory
					.newVariableDeclarationNode(
							newSource(parallelNode,
									CivlcTokenConstant.DECLARATION),
							nodeFactory.newIdentifierNode(
									newSource(domainDeclaration,
											CivlcTokenConstant.IDENTIFIER),
									OMPPRE + "dom"),
							nodeFactory
									.newDomainTypeNode(
											newSource(domainDeclaration,
													CivlcTokenConstant.DOMAIN),
											nodeFactory
													.newIntegerConstantNode(
															newSource(
																	domainDeclaration,
																	CivlcTokenConstant.INTEGER_CONSTANT),
															"1")), cln);
			items.add(loopDomain);

			// Declaring $omp_gteam gteam = $omp_gteam_create($here, nthreads);
			gteamVar = this.gteamDeclaration();
			items.add(gteamVar);

			// Get list of shared, private, and firstPrivate variables from the
			// OmpParallelNode
			sharedList = ((OmpParallelNode) node).sharedList();
			removeNodeFromParent(sharedList);
			privateList = ((OmpParallelNode) node).privateList();
			removeNodeFromParent(privateList);
			firstPrivateList = ((OmpParallelNode) node).firstprivateList();
			removeNodeFromParent(firstPrivateList);

			// Add implicit shared variables
			ArrayList<String> alreadyDeclVars = new ArrayList<String>();
			alreadyDeclVars.add("stdin");
			alreadyDeclVars.add("stdout");
			alreadyDeclVars.add("stderr");

			// Add varaible to already declared variables to decide what is to
			// be shared or private
			if (sharedList != null) {
				for (ASTNode child : sharedList.children()) {
					String c = ((IdentifierExpressionNode) child)
							.getIdentifier().name();
					alreadyDeclVars.add(c);
				}
			}

			if (privateList != null) {
				for (ASTNode child : privateList.children()) {
					String c = ((IdentifierExpressionNode) child)
							.getIdentifier().name();
					alreadyDeclVars.add(c);
				}
			}

			if (threadPrivateIDs != null) {
				for (ASTNode child : threadPrivateIDs.children()) {
					String c = ((IdentifierExpressionNode) child)
							.getIdentifier().name();
					alreadyDeclVars.add(c);
				}
			}

			if (firstPrivateList != null) {
				for (ASTNode child : firstPrivateList.children()) {
					String c = ((IdentifierExpressionNode) child)
							.getIdentifier().name();
					alreadyDeclVars.add(c);
				}
			}

			ArrayList<String> implicitShared = new ArrayList<String>();
			if (sharedList == null) {
				List<IdentifierExpressionNode> list = new LinkedList<>();
				sharedList = nodeFactory.newSequenceNode(
						newSource("sharedList",
								CivlcTokenConstant.ARGUMENT_LIST),
						"sharedList", list);
			}
			ArrayList<String> loopVars = new ArrayList<String>();
			// Get implicit shared variable and remove any that are already
			// declared
			boolean removed = getImplicitShared(sharedList, node,
					alreadyDeclVars, implicitShared, loopVars, false);

			if (removed) {
				List<IdentifierExpressionNode> list = new LinkedList<IdentifierExpressionNode>();
				for (IdentifierExpressionNode id : sharedList) {
					if (id != null) {
						ASTNode parent = id.parent();
						int index = id.childIndex();
						parent.removeChild(index);
						list.add(id);
					}
				}
				sharedList = nodeFactory.newSequenceNode(
						newSource("sharedList",
								CivlcTokenConstant.ARGUMENT_LIST),
						"sharedList", list);
			}

			if (privateList == null) {
				List<IdentifierExpressionNode> list = new LinkedList<>();
				privateList = nodeFactory.newSequenceNode(
						newSource("privateList",
								CivlcTokenConstant.ARGUMENT_LIST),
						"privateList", list);
			}

			ArrayList<String> loopVariables = new ArrayList<String>();

			// Get variables from the loop and remove them from the list as
			// they are not to be treated liek shared variables
			getLoopVariables(node, alreadyDeclVars, privateList);
			removed = false;
			for (String varName : loopVariables) {
				for (IdentifierExpressionNode id : sharedList) {
					if (id != null) {
						if (id.getIdentifier().name().equals(varName)) {
							int index = id.childIndex();
							sharedList.removeChild(index);
							removed = true;
						}
					}

				}
			}

			for (IdentifierExpressionNode child : sharedList) {
				IdentifierNode id = child.getIdentifier();
				Type currentType = ((Variable) id.getEntity()).getType();
				if (currentType instanceof StructureOrUnionType) {
					String tag = ((StructureOrUnionType) currentType).getTag();
					if (tag.equals("omp_lock_t")) {
						child.remove();
						removed = true;
					}
				} else if (currentType instanceof QualifiedObjectType) {
					if (((QualifiedObjectType) currentType).isInputQualified()) {
						child.remove();
						removed = true;
					}
				}
			}

			if (removed) {
				List<IdentifierExpressionNode> list = new LinkedList<IdentifierExpressionNode>();
				for (IdentifierExpressionNode id : sharedList) {
					if (id != null) {
						ASTNode parent = id.parent();
						int index = id.childIndex();
						parent.removeChild(index);
						list.add(id);
					}
				}
				sharedList = nodeFactory.newSequenceNode(
						newSource("sharedList",
								CivlcTokenConstant.ARGUMENT_LIST),
						"sharedList", list);
			}

			// Get list of reduction variables from the OmpParallelNode
			OmpSymbolReductionNode reductionNode = null;
			ompReductionNode = ((OmpParallelNode) node).reductionList();
			removeNodeFromParent(ompReductionNode);
			if (ompReductionNode != null) {
				reductionNode = (OmpSymbolReductionNode) ompReductionNode
						.child(0);
				reductionList = (SequenceNode<IdentifierExpressionNode>) reductionNode
						.child(0);
			}

			// Declaring $omp_gshared x_gshared = $omp_gshared_create(gteam, &x)
			// for each shared variable "x"
			if (sharedList != null) {
				for (ASTNode child : sharedList.children()) {
					if (child != null) {
						VariableDeclarationNode gsharedVar;
						IdentifierNode c = ((IdentifierExpressionNode) child)
								.getIdentifier();

						gsharedVar = this.gsharedDeclaration(c);
						items.add(gsharedVar);
					}
				}
			}

			CivlForNode cfn;

			// Create the ForLoopInitializerNode for the CIVLForNode
			String parFor = "parFor";
			ForLoopInitializerNode initializerNode;
			initializerNode = nodeFactory
					.newForLoopInitializerNode(
							newSource(parFor,
									CivlcTokenConstant.INITIALIZER_LIST),
							Arrays.asList(nodeFactory
									.newVariableDeclarationNode(
											newSource(
													parFor,
													CivlcTokenConstant.DECLARATION),
											nodeFactory
													.newIdentifierNode(
															newSource(
																	parFor,
																	CivlcTokenConstant.IDENTIFIER),
															TID),
											nodeFactory
													.newBasicTypeNode(
															newSource(
																	parFor,
																	CivlcTokenConstant.INT),
															BasicTypeKind.INT))));

			List<BlockItemNode> parForItems = new LinkedList<>();

			// $omp_team team = $omp_team_create($here, gteam, _tid);
			parForItems.add(teamDeclaration());

			// Create local and status variables for each shared variable
			if (sharedList != null) {
				for (ASTNode child : sharedList.children()) {
					if (child != null) {
						VariableDeclarationNode localSharedVar;
						VariableDeclarationNode statusSharedVar;

						IdentifierNode c = (IdentifierNode) child.child(0);
						String localDeclaration = "LocalSharedVarDeclaration";
						String statusDeclaration = "StatusSharedVarDeclaration";
						TypeNode privateType = ((VariableDeclarationNode) ((Variable) c
								.getEntity()).getFirstDeclaration())
								.getTypeNode().copy();
						if (privateType.isInputQualified()) {
							privateType.setInputQualified(false);
						}
						IdentifierNode localSharedIdentifer = nodeFactory
								.newIdentifierNode(
										newSource(c.name() + localDeclaration,
												CivlcTokenConstant.IDENTIFIER),
										OMPPRE + c.name() + "_local");
						IdentifierNode statusSharedIdentifer = nodeFactory
								.newIdentifierNode(
										newSource(c.name() + statusDeclaration,
												CivlcTokenConstant.IDENTIFIER),
										OMPPRE + c.name() + "_status");
						Type currentType = ((Variable) c.getEntity()).getType();

						if (privateType instanceof ArrayTypeNode
								&& currentType instanceof PointerType) {
							if (!(((PointerType) currentType).referencedType() instanceof ArrayType)) {
								currentType = ((PointerType) currentType)
										.referencedType();
								while (currentType instanceof ArrayType) {
									currentType = ((ArrayType) currentType)
											.getElementType();
								}
								BasicTypeKind baseTypeKind = ((StandardBasicType) currentType)
										.getBasicTypeKind();

								privateType = nodeFactory
										.newPointerTypeNode(
												newSource(c.name() + "type",
														CivlcTokenConstant.TYPE),
												nodeFactory
														.newBasicTypeNode(
																newSource(
																		localDeclaration,
																		CivlcTokenConstant.TYPE),
																baseTypeKind));
							}
						}

						localSharedVar = nodeFactory
								.newVariableDeclarationNode(
										newSource(localDeclaration,
												CivlcTokenConstant.DECLARATION),
										localSharedIdentifer, privateType);

						TypeNode statusType = privateType.copy();
						TypeNode baseStatusType = statusType;

						while (statusType instanceof ArrayTypeNode
								&& statusType.child(0) instanceof ArrayTypeNode) {
							statusType = (TypeNode) statusType.child(0);
						}
						if (statusType instanceof ArrayTypeNode) {
							statusType.setChild(0, nodeFactory
									.newBasicTypeNode(
											newSource(statusDeclaration,
													CivlcTokenConstant.INT),
											BasicTypeKind.INT));
							statusSharedVar = nodeFactory
									.newVariableDeclarationNode(
											newSource(
													statusDeclaration,
													CivlcTokenConstant.DECLARATION),
											statusSharedIdentifer,
											baseStatusType);

						} else if (statusType instanceof PointerTypeNode) {
							statusType.setChild(0, nodeFactory
									.newBasicTypeNode(
											newSource(statusDeclaration,
													CivlcTokenConstant.INT),
											BasicTypeKind.INT));
							statusSharedVar = nodeFactory
									.newVariableDeclarationNode(
											newSource(
													statusDeclaration,
													CivlcTokenConstant.DECLARATION),
											statusSharedIdentifer,
											baseStatusType);
						} else if (currentType instanceof StructureOrUnionType
								&& statusType instanceof TypedefNameNode) {
							TypedefNameNode status = (TypedefNameNode) statusType
									.copy();
							status.setName(nodeFactory.newIdentifierNode(
									newSource(statusDeclaration,
											CivlcTokenConstant.DECLARATION),
									status.getName().name() + "_status"));
							statusSharedVar = nodeFactory
									.newVariableDeclarationNode(
											newSource(
													statusDeclaration,
													CivlcTokenConstant.DECLARATION),
											statusSharedIdentifer, status);

							TypedefDeclarationNode structDef = nodeFactory
									.newTypedefDeclarationNode(
											newSource(
													statusDeclaration,
													CivlcTokenConstant.DECLARATION),
											nodeFactory
													.newIdentifierNode(
															newSource(
																	statusDeclaration,
																	CivlcTokenConstant.DECLARATION),
															status.getName()
																	.name()),
											nodeFactory
													.newStructOrUnionTypeNode(
															newSource(
																	statusDeclaration,
																	CivlcTokenConstant.DECLARATION),
															true,
															nodeFactory
																	.newIdentifierNode(
																			newSource(
																					statusDeclaration,
																					CivlcTokenConstant.DECLARATION),
																			status.getName()
																					.name()),
															null));

							boolean toAdd = true;
							for (TypedefDeclarationNode typeDefNode : structsDefsToAdd) {
								if (typeDefNode.getName().equals(
										structDef.getName())) {
									toAdd = false;
								}
							}
							if (toAdd) {
								structsDefsToAdd.add(structDef);
							}

							StructureOrUnionType structType = (StructureOrUnionType) currentType;
							Iterable<Field> fields = structType.getFields();

							List<FieldDeclarationNode> fieldList = new LinkedList<FieldDeclarationNode>();

							for (Field field : fields) {
								IdentifierNode fieldName = nodeFactory
										.newIdentifierNode(
												newSource(
														statusDeclaration,
														CivlcTokenConstant.DECLARATION),
												field.getName());

								TypeNode intType = nodeFactory
										.newBasicTypeNode(
												newSource(statusDeclaration,
														CivlcTokenConstant.INT),
												BasicTypeKind.INT);

								FieldDeclarationNode fieldToAdd = nodeFactory
										.newFieldDeclarationNode(
												newSource(
														statusDeclaration,
														CivlcTokenConstant.DECLARATION),
												fieldName, intType);

								fieldList.add(fieldToAdd);
							}

							SequenceNode<FieldDeclarationNode> structDeclList = nodeFactory
									.newSequenceNode(
											newSource(
													statusDeclaration,
													CivlcTokenConstant.DECLARATION),
											"fieldList", fieldList);

							StructureOrUnionTypeNode structTypeToAdd = nodeFactory
									.newStructOrUnionTypeNode(
											newSource(
													statusDeclaration,
													CivlcTokenConstant.DECLARATION),
											true,
											nodeFactory
													.newIdentifierNode(
															newSource(
																	statusDeclaration,
																	CivlcTokenConstant.DECLARATION),
															status.getName()
																	.name()),
											structDeclList);

							toAdd = true;
							for (StructureOrUnionTypeNode typeNode : structsToAdd) {

								if (typeNode.getName().equals(
										structTypeToAdd.getName())) {
									toAdd = false;
								}

							}
							if (toAdd) {
								structsToAdd.add(structTypeToAdd);
							}

						} else {
							statusSharedVar = nodeFactory
									.newVariableDeclarationNode(
											newSource(
													statusDeclaration,
													CivlcTokenConstant.DECLARATION),
											statusSharedIdentifer,
											nodeFactory
													.newBasicTypeNode(
															newSource(
																	statusDeclaration,
																	CivlcTokenConstant.INT),
															BasicTypeKind.INT));
						}

						parForItems.add(localSharedVar);
						parForItems.add(statusSharedVar);
					}
				}
			}

			// Declare $omp_shared x_shared = $omp_shared_create(team,
			// x_gshared, void *local, void, *status)
			// for each shared variable "x"
			if (sharedList != null) {
				for (ASTNode child : sharedList.children()) {
					if (child != null) {
						VariableDeclarationNode sharedVar;
						IdentifierNode c = ((IdentifierExpressionNode) child)
								.getIdentifier();

						sharedVar = this.sharedDeclaration(c);
						parForItems.add(sharedVar);
					}
				}
			}

			// Add firstprivate variable declarations
			if (firstPrivateList != null) {
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
				for (ASTNode child : privateList.children()) {
					VariableDeclarationNode localPrivate = addPrivateVariable(
							(IdentifierExpressionNode) child, "regular");
					parForItems.add(localPrivate);
				}
			}

			// Add all children to the $par_for body
			int i = 0;
			for (ASTNode child : children) {
				node.removeChild(i);
				parForItems.add((BlockItemNode) child);
				i++;
			}

			// Apply association operator to all reduction variables
			if (reductionList != null) {
				for (ASTNode child : reductionList.children()) {
					String name = ((IdentifierNode) child.child(0)).name();
					String operator = reductionNode.operator().name();
					parForItems.add(applyAssoc(name, operator));
				}
			}

			// $omp_barrier_and_flush(team);
			parForItems.add(barrierAndFlush(TEAM));

			// $omp_shared_destroy(x_shared);
			// for each shared variable "x"
			if (sharedList != null) {
				for (ASTNode child : sharedList.children()) {
					if (child != null) {
						IdentifierNode c = ((IdentifierExpressionNode) child)
								.getIdentifier();

						parForItems.add(destroy("shared", OMPPRE + c.name()
								+ "_shared"));
					}
				}
			}

			// $omp_team_destroy(team);
			parForItems.add(destroy("team", TEAM));

			StatementNode parForBody;
			parForBody = nodeFactory.newCompoundStatementNode(
					newSource(parFor, CivlcTokenConstant.COMPOUND_STATEMENT),
					parForItems);

			// Create $par_for loop
			cfn = nodeFactory.newCivlForNode(
					newSource(parallelNode, CivlcTokenConstant.CIVLFOR), true,
					(DeclarationListNode) initializerNode, this
							.identifierExpression(
									newSource(parFor,
											CivlcTokenConstant.IDENTIFIER),
									OMPPRE + "dom"), parForBody, null);

			int childrenAdded = items.size();

			// Add $par_for to the body
			items.add(cfn);

			// $omp_shared_destroy(x_gshared);
			// for each shared variable "x"
			if (sharedList != null) {
				for (ASTNode child : sharedList.children()) {
					if (child != null) {
						IdentifierNode c = ((IdentifierExpressionNode) child)
								.getIdentifier();

						items.add(destroy("gshared", OMPPRE + c.name()
								+ "_gshared"));
					}
				}
			}

			// $omp_gteam_destroy(gteam);
			items.add(destroy("gteam", GTEAM));

			// Create the CompoundStatementNode of that replaces the
			// OmpParallelNode
			pragmaBody = nodeFactory.newCompoundStatementNode(
					newSource(parallelNode, COmpParser.PARALLEL), items);

			// Insert the CompoundStatementNode where the OmpParallelNode used
			// to be
			int index = node.childIndex();
			ASTNode parent = node.parent();
			parent.setChild(index, pragmaBody);
			children = pragmaBody.children();

			// Visit all the child to check for omp code
			for (ASTNode child : children) {
				if (child.childIndex() >= childrenAdded) {
					replaceOMPPragmas(child, privateList, sharedList,
							reductionList, firstPrivateList, threadPrivateIDs);
				}
			}
		} else if (node instanceof OmpForNode) {
			// Check if the node is a OmpForNode and transform the node
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
			ArrayList<Triple<ASTNode, ASTNode, ASTNode>> ranges = new ArrayList<>();
			ArrayList<IdentifierNode> loopVariables = new ArrayList<IdentifierNode>();
			SequenceNode<IdentifierExpressionNode> firstPrivateList, lastPrivateList;
			ForLoopNode currentLoop = null;
			ForLoopInitializerNode initializer;
			OmpSymbolReductionNode reductionNode = null;
			String forNode = "forPragma";

			// Get the list of reduction variables in the OmpForNode
			ompReductionNode = ((OmpForNode) node).reductionList();
			removeNodeFromParent(ompReductionNode);
			if (ompReductionNode != null) {
				reductionNode = (OmpSymbolReductionNode) ompReductionNode
						.child(0);
				reductionList = (SequenceNode<IdentifierExpressionNode>) reductionNode
						.child(0);
			}

			// Get the list of first private variables in the OmpForNode
			firstPrivateList = ((OmpForNode) node).firstprivateList();
			removeNodeFromParent(firstPrivateList);

			// Get the list of last private variables in the OmpForNode
			lastPrivateList = ((OmpForNode) node).lastprivateList();
			removeNodeFromParent(lastPrivateList);

			for (int i = 0; i < collapseLevel; i++) {
				Triple<ASTNode, ASTNode, ASTNode> lo_hi_step;

				if (i == 0) {
					currentLoop = (ForLoopNode) node.child(7);
					body = currentLoop.child(1);
				} else {
					currentLoop = (ForLoopNode) currentLoop.getBody();
					body = currentLoop.child(1);
				}
				initializer = currentLoop.getInitializer();
				lo_hi_step = canonicalForLoopBounds(currentLoop);
				ranges.add(new Triple<ASTNode, ASTNode, ASTNode>(
						lo_hi_step.first, lo_hi_step.second, lo_hi_step.third));
				// Initializer node only will be either IdentifierExpressionNode
				// or DeclarationNode.
				// The first child of the first child of both of them is
				// identifier node.
				loopVariables.add((IdentifierNode) initializer.child(0)
						.child(0));
			}
			// For each of the ranges create a range variable
			int rangeNumber = 0;
			for (Triple<ASTNode, ASTNode, ASTNode> triple : ranges) {
				VariableDeclarationNode threadRange;
				String range = "rangeDeclaration";
				threadRange = nodeFactory
						.newVariableDeclarationNode(
								newSource(forNode,
										CivlcTokenConstant.DECLARATION),
								nodeFactory
										.newIdentifierNode(
												newSource(
														range,
														CivlcTokenConstant.IDENTIFIER),
												OMPPRE
														+ "r"
														+ Integer
																.toString(rangeNumber + 1)),
								nodeFactory.newRangeTypeNode(newSource(range,
										CivlcTokenConstant.RANGE)),
								nodeFactory.newRegularRangeNode(
										newSource(range,
												CivlcTokenConstant.RANGE),
										(ExpressionNode) triple.first.copy(),
										(ExpressionNode) triple.second.copy(),
										(ExpressionNode) triple.third.copy()));
				items.add(threadRange);
				rangeNumber++;
			}

			// Create the right hand side of the domain variable declaration
			List<PairNode<DesignationNode, InitializerNode>> initList = new ArrayList<PairNode<DesignationNode, InitializerNode>>();

			String domainDeclaration = "domainDeclaration";

			for (int k = 1; k < rangeNumber + 1; k++) {
				initList.add(nodeFactory
						.newPairNode(
								newSource(domainDeclaration,
										CivlcTokenConstant.STRUCT),
								(DesignationNode) null,
								(InitializerNode) this.identifierExpression(
										newSource(domainDeclaration,
												CivlcTokenConstant.IDENTIFIER),
										OMPPRE + "r" + Integer.toString(k))));
			}

			CompoundInitializerNode temp = nodeFactory
					.newCompoundInitializerNode(
							newSource(domainDeclaration,
									CivlcTokenConstant.INITIALIZER_LIST),
							initList);
			CompoundLiteralNode cln = nodeFactory.newCompoundLiteralNode(
					newSource(domainDeclaration,
							CivlcTokenConstant.COMPOUND_LITERAL), nodeFactory
							.newDomainTypeNode(newSource(domainDeclaration,
									CivlcTokenConstant.DOMAIN)), temp);

			// If there is only 1 child then make that the children
			// Else get the list from the OmpForNode body
			if (body instanceof CompoundStatementNode) {
				children = body.children();
			} else {
				ArrayList<ASTNode> tempList = new ArrayList<ASTNode>();
				tempList.add(body);
				Iterable<ASTNode> tempIterable = tempList;
				children = (Iterable<ASTNode>) tempIterable;
			}

			// Create loop_domain variable
			loopDomain = nodeFactory
					.newVariableDeclarationNode(
							newSource(forNode, CivlcTokenConstant.DECLARATION),
							nodeFactory.newIdentifierNode(
									newSource(domainDeclaration,
											CivlcTokenConstant.IDENTIFIER),
									OMPPRE + "loop_domain"),
							nodeFactory
									.newDomainTypeNode(
											newSource(domainDeclaration,
													CivlcTokenConstant.DOMAIN),
											nodeFactory
													.newIntegerConstantNode(
															newSource(
																	domainDeclaration,
																	CivlcTokenConstant.INTEGER_CONSTANT),
															"1")), cln);
			items.add(loopDomain);

			int loopDecomp = config.ompLoopDecomp();

			// ($domain(1))$omp_arrive_loop(team, int, loop_domain, strategy)
			String myItersPlace = "myItersDeclaration";
			ExpressionNode ompArriveLoop = nodeFactory
					.newCastNode(
							newSource(myItersPlace, CivlcTokenConstant.CAST),
							nodeFactory
									.newDomainTypeNode(
											newSource(myItersPlace,
													CivlcTokenConstant.DOMAIN),
											nodeFactory
													.newIntegerConstantNode(
															newSource(
																	myItersPlace,
																	CivlcTokenConstant.INTEGER_CONSTANT),
															Integer.toString(collapseLevel))),
							nodeFactory.newFunctionCallNode(
									newSource(myItersPlace,
											CivlcTokenConstant.CALL),
									this.identifierExpression(
											newSource(
													myItersPlace,
													CivlcTokenConstant.IDENTIFIER),
											"$omp_arrive_loop"),
									Arrays.asList(
											this.identifierExpression(
													newSource(
															myItersPlace,
															CivlcTokenConstant.IDENTIFIER),
													TEAM),
											nodeFactory
													.newIntegerConstantNode(
															newSource(
																	myItersPlace,
																	CivlcTokenConstant.INTEGER_CONSTANT),
															this.ompArriveLoopCounter
																	+ ""),
											nodeFactory
													.newCastNode(
															newSource(
																	myItersPlace,
																	CivlcTokenConstant.CAST),
															nodeFactory
																	.newDomainTypeNode(newSource(
																			myItersPlace,
																			CivlcTokenConstant.DOMAIN)),
															this.identifierExpression(
																	newSource(
																			myItersPlace,
																			CivlcTokenConstant.IDENTIFIER),
																	OMPPRE
																			+ "loop_domain")),
											nodeFactory
													.newIntegerConstantNode(
															newSource(
																	myItersPlace,
																	CivlcTokenConstant.INTEGER_CONSTANT),
															String.valueOf(loopDecomp))),
									null));
			this.ompArriveLoopCounter++;
			// Get correct level "n" for domain(n)
			IntegerConstantNode domainLevel = nodeFactory
					.newIntegerConstantNode(
							newSource(myItersPlace,
									CivlcTokenConstant.INTEGER_CONSTANT),
							String.valueOf(collapseLevel));

			// Add $domain(1) my_iters = ($domain(1))$omp_arrive_loop(team,
			// loop_domain);
			VariableDeclarationNode myIters;
			myIters = nodeFactory.newVariableDeclarationNode(
					newSource(forNode, CivlcTokenConstant.DECLARATION),
					nodeFactory.newIdentifierNode(
							newSource(myItersPlace,
									CivlcTokenConstant.IDENTIFIER), OMPPRE
									+ "my_iters"), nodeFactory
							.newDomainTypeNode(
									newSource(myItersPlace,
											CivlcTokenConstant.DOMAIN),
									domainLevel), ompArriveLoop);
			items.add(myIters);

			// Add firstprivate variable declarations
			if (firstPrivateList != null) {
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

			// Declare local copies of the private variables
			if (lastPrivateList != null) {
				for (ASTNode child : lastPrivateList.children()) {
					VariableDeclarationNode localPrivate = addPrivateVariable(
							(IdentifierExpressionNode) child, "regular");
					items.add(localPrivate);
				}
			}

			String civlFor = "civlFor";
			CivlForNode cfn;

			List<VariableDeclarationNode> declarations = new ArrayList<VariableDeclarationNode>();
			for (IdentifierNode var : loopVariables) {
				declarations.add(nodeFactory.newVariableDeclarationNode(
						newSource(civlFor, CivlcTokenConstant.DECLARATION), var
								.copy(), nodeFactory.newBasicTypeNode(
								newSource(civlFor, CivlcTokenConstant.INT),
								BasicTypeKind.INT)));
			}

			initializerNode = nodeFactory.newForLoopInitializerNode(
					newSource(civlFor, CivlcTokenConstant.INITIALIZER_LIST),
					declarations);

			// Get the body of the OmpForNode and go down for loop children if
			// there is a collapse clause
			for (int i = 0; i < collapseLevel; i++) {
				if (i == 0) {
					currentLoop = (ForLoopNode) node.child(7);
				} else {
					currentLoop = (ForLoopNode) currentLoop.getBody();
				}
			}

			// Remove children from original for body and add to new for loop
			int i = 0;
			for (ASTNode child : children) {
				if (body instanceof CompoundStatementNode) {
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
			forBody = nodeFactory.newCompoundStatementNode(
					newSource(civlFor, CivlcTokenConstant.COMPOUND_STATEMENT),
					forItems);

			// Create $for node with the original for body as its body
			cfn = nodeFactory.newCivlForNode(
					newSource(forNode, CivlcTokenConstant.CIVLFOR), false,
					(DeclarationListNode) initializerNode,
					nodeFactory.newIdentifierExpressionNode(
							newSource(civlFor,
									CivlcTokenConstant.INITIALIZER_LIST),
							nodeFactory.newIdentifierNode(
									newSource(civlFor,
											CivlcTokenConstant.IDENTIFIER),
									OMPPRE + "my_iters")), forBody, null);
			items.add(cfn);

			// Apply association operator to all reduction variables
			if (reductionList != null) {
				for (ASTNode child : reductionList.children()) {
					String name = ((IdentifierNode) child.child(0)).name();
					String operator = reductionNode.operator().name();
					items.add(applyAssoc(name, operator));
				}
			}

			// $barrier_and_flush(team);
			if (!((OmpForNode) node).nowait()) {
				items.add(barrierAndFlush(TEAM));
			}

			// Do lastprivate vars
			if (lastPrivateList != null) {
				for (ASTNode child : lastPrivateList.children()) {
					String name = ((IdentifierNode) child.child(0)).name();
					ExpressionNode arg1 = this.identifierExpression(
							newSource("lastPrivate",
									CivlcTokenConstant.IDENTIFIER), OMPPRE
									+ name + "$_private");
					OperatorNode expression = nodeFactory.newOperatorNode(
							newSource("lastPrivate", CivlcTokenConstant.EXPR),
							Operator.ASSIGN, (ExpressionNode) child.copy(),
							arg1);
					ExpressionStatementNode statement = nodeFactory
							.newExpressionStatementNode(expression);

					int size = items.size();

					ASTNode lastChild = items.get(size - 1);

					Pair<VariableDeclarationNode, ExpressionStatementNode> tempPair = new Pair<>(
							null, statement);
					if (sharedWrite.containsKey(lastChild)) {
						ArrayList<Pair<VariableDeclarationNode, ExpressionStatementNode>> nodeToAdd = sharedRead
								.get(lastChild);
						nodeToAdd.add(tempPair);
					} else {
						ArrayList<Pair<VariableDeclarationNode, ExpressionStatementNode>> tempPairs = new ArrayList<Pair<VariableDeclarationNode, ExpressionStatementNode>>();
						tempPairs.add(tempPair);
						sharedWrite.put(lastChild, tempPairs);
					}
				}
			}

			boolean removed = false;
			if (sharedIDs != null) {
				for (ASTNode child : sharedIDs.children()) {
					IdentifierExpressionNode idexp = (IdentifierExpressionNode) child;
					IdentifierNode id = idexp.getIdentifier();
					if (lastPrivateList != null) {
						for (ASTNode childPrivateList : lastPrivateList
								.children()) {
							IdentifierExpressionNode privateIdexp = (IdentifierExpressionNode) childPrivateList;
							IdentifierNode privateId = privateIdexp
									.getIdentifier();
							if (id.name().equals(privateId.name())) {
								child.remove();
								removed = true;
							}
						}
					}

				}
			}
			SequenceNode<IdentifierExpressionNode> newSharedList;
			List<IdentifierExpressionNode> list = new LinkedList<IdentifierExpressionNode>();
			if (removed) {
				for (ASTNode child : sharedIDs.children()) {
					if (child != null) {
						child.remove();
						list.add((IdentifierExpressionNode) child);
					}
				}
				newSharedList = nodeFactory.newSequenceNode(
						newSource("sharedList",
								CivlcTokenConstant.IDENTIFIER_LIST),
						"sharedList", list);
				sharedIDs = newSharedList;
			}

			if (lastPrivateList != null) {
				for (ASTNode child : lastPrivateList.children()) {
					if (child != null) {
						child.remove();
						privateIDs
								.addSequenceChild((IdentifierExpressionNode) child);
					}
				}
			}

			// Insert the CompoundStatementNode where the OmpForNode used to be
			pragmaBody = nodeFactory.newCompoundStatementNode(
					newSource(forNode, CivlcTokenConstant.COMPOUND_STATEMENT),
					items);
			children = pragmaBody.children();
			int index = node.childIndex();
			ASTNode parent = node.parent();
			parent.setChild(index, pragmaBody);

			// Visit all of the children to check for omp code
			for (ASTNode child : children) {
				replaceOMPPragmas(child, privateIDs, sharedIDs, reductionIDs,
						firstPrivateIDs, threadPrivateIDs);
			}

		} else if (node instanceof OmpSyncNode) {
			String syncKind = ((OmpSyncNode) node).ompSyncNodeKind().toString();
			CompoundStatementNode body;
			LinkedList<BlockItemNode> items = new LinkedList<>();
			// Check the synckind
			if (syncKind.equals("MASTER")) {
				String syncNode = "masterNode";
				// Replace omp master with a check if _tid==0 and insert the omp
				// master body into that
				List<ExpressionNode> operands = new ArrayList<ExpressionNode>();
				operands.add(nodeFactory.newIdentifierExpressionNode(
						newSource(syncNode, CivlcTokenConstant.IDENTIFIER),
						nodeFactory.newIdentifierNode(
								newSource(syncNode,
										CivlcTokenConstant.IDENTIFIER), TID)));
				operands.add(nodeFactory
						.newIntegerConstantNode(
								newSource(syncNode,
										CivlcTokenConstant.INTEGER_CONSTANT),
								"0"));
				int i = 0;
				for (ASTNode child : node.children()) {
					node.removeChild(i);
					items.add((BlockItemNode) child);
					i++;
				}
				body = nodeFactory.newCompoundStatementNode(
						newSource(syncNode,
								CivlcTokenConstant.COMPOUND_STATEMENT), items);
				IfNode ifStatement = nodeFactory.newIfNode(
						newSource(syncNode, CivlcTokenConstant.IF), nodeFactory
								.newOperatorNode(
										newSource(syncNode,
												CivlcTokenConstant.EQUALS),
										Operator.EQUALS, operands), body);
				// Replace omp master with the new if statement
				int index = node.childIndex();
				ASTNode parent = node.parent();
				parent.setChild(index, ifStatement);

				Iterable<ASTNode> children = body.children();

				// Visit all the child to check for omp code
				for (ASTNode child : children) {
					replaceOMPPragmas(child, privateIDs, sharedIDs,
							reductionIDs, firstPrivateIDs, threadPrivateIDs);
				}

			} else if (syncKind.equals("OMPATOMIC")) {
				String atomicSrc = "ompAtomic";
				AtomicNode atomicNode;

				int i = 0;
				for (ASTNode child : node.children()) {
					if (child instanceof CompoundStatementNode) {
						int j = 0;
						for (ASTNode child2 : child.children()) {
							child.removeChild(j);
							items.add((BlockItemNode) child2);
							j++;
						}
						node.removeChild(i);
						i++;
					} else {
						node.removeChild(i);
						items.add((BlockItemNode) child);
						i++;
					}
				}

				body = nodeFactory.newCompoundStatementNode(
						newSource(atomicSrc,
								CivlcTokenConstant.COMPOUND_STATEMENT), items);

				atomicNode = nodeFactory.newAtomicStatementNode(
						newSource(atomicSrc, CivlcTokenConstant.ATOMIC), false,
						body);

				int index = node.childIndex();
				ASTNode parent = node.parent();
				parent.setChild(index, atomicNode);

				Iterable<ASTNode> children = body.children();

				// Visit all the child to check for omp code
				for (ASTNode child : children) {
					replaceOMPPragmas(child, privateIDs, sharedIDs,
							reductionIDs, firstPrivateIDs, threadPrivateIDs);
				}
			} else if (syncKind.equals("BARRIER")) {
				// Replace omp barrier with $omp_barrier_and_flush
				ExpressionStatementNode barrierAndFlush = barrierAndFlush(TEAM);
				int index = node.childIndex();
				ASTNode parent = node.parent();
				parent.setChild(index, barrierAndFlush);
			} else if (syncKind.equals("CRITICAL")) {
				// For an omp critical, check if there is a name for the
				// critical
				// If there is a name, get the name. Else, give it noname
				Iterable<ASTNode> children = node.children();
				String syncNode = "criticalNode";
				IdentifierNode criticalIDName = ((OmpSyncNode) node)
						.criticalName();
				removeNodeFromParent(criticalIDName);
				String criticalName = null;
				if (criticalIDName != null) {
					criticalName = "_critical_" + criticalIDName.name();
				} else {
					criticalName = "_critical_noname";
				}

				// Create expression and body of when node
				ExpressionNode notCritical = nodeFactory.newOperatorNode(
						newSource(syncNode, CivlcTokenConstant.NOT),
						Operator.NOT, Arrays.asList(this.identifierExpression(
								newSource(syncNode,
										CivlcTokenConstant.IDENTIFIER),
								criticalName)));
				ExpressionStatementNode criticalTrue = nodeFactory
						.newExpressionStatementNode(nodeFactory.newOperatorNode(
								newSource(syncNode, CivlcTokenConstant.ASSIGN),
								Operator.ASSIGN,
								Arrays.asList(
										this.identifierExpression(
												newSource(
														syncNode,
														CivlcTokenConstant.IDENTIFIER),
												criticalName),
										nodeFactory
												.newBooleanConstantNode(
														newSource(
																syncNode,
																CivlcTokenConstant.TRUE),
														true))));

				// Create and add when node
				// $when (!_critical_a) _critical_a=$true;
				items.add(nodeFactory.newWhenNode(
						newSource(syncNode, CivlcTokenConstant.WHEN),
						notCritical, criticalTrue));
				// Put critical section body in the when body.
				int i = 0;
				for (ASTNode child : node.children()) {
					node.removeChild(i);
					items.add((BlockItemNode) child);
					i++;
				}
				items.add(nodeFactory.newExpressionStatementNode(nodeFactory
						.newFunctionCallNode(
								newSource("flush", CivlcTokenConstant.CALL),
								this.identifierExpression("$omp_flush_all"),
								Arrays.asList(this.identifierExpression(TEAM)),
								null)));
				// Make the critical variable false now
				ExpressionStatementNode criticalFalse = nodeFactory
						.newExpressionStatementNode(nodeFactory.newOperatorNode(
								newSource(syncNode, CivlcTokenConstant.ASSIGN),
								Operator.ASSIGN,
								Arrays.asList(
										this.identifierExpression(
												newSource(
														syncNode,
														CivlcTokenConstant.IDENTIFIER),
												criticalName),
										nodeFactory
												.newBooleanConstantNode(
														newSource(
																syncNode,
																CivlcTokenConstant.FALSE),
														false))));
				items.add(criticalFalse);

				// Add body to the CompoundstatementNode and replace the omp
				// critical node with the CompoundStatementNode
				body = nodeFactory.newCompoundStatementNode(
						newSource(syncNode,
								CivlcTokenConstant.COMPOUND_STATEMENT), items);
				if (!criticalNames.contains(criticalName)) {
					criticalNames.add(criticalName);
				}
				int index = node.childIndex();
				ASTNode parent = node.parent();
				parent.setChild(index, body);

				children = body.children();

				// Visit all the child to check for omp code
				for (ASTNode child : children) {
					replaceOMPPragmas(child, privateIDs, sharedIDs,
							reductionIDs, firstPrivateIDs, threadPrivateIDs);
				}

			}
		} else if (node instanceof OmpWorksharingNode) {
			Iterable<ASTNode> children = node.children();
			String workshareKind = ((OmpWorksharingNode) node)
					.ompWorkshareNodeKind().toString();
			CompoundStatementNode body;
			LinkedList<BlockItemNode> items = new LinkedList<>();
			if (workshareKind.equals("SECTIONS")) {
				String sectionsPlace = "sections";
				SequenceNode<IdentifierExpressionNode> privateList = ((OmpWorksharingNode) node)
						.privateList();
				removeNodeFromParent(privateList);
				firstPrivateIDs = ((OmpWorksharingNode) node)
						.firstprivateList();
				removeNodeFromParent(firstPrivateIDs);
				int numberSections = 0;
				CompoundStatementNode pragmaBody = (CompoundStatementNode) node
						.child(7);
				ArrayList<LinkedList<BlockItemNode>> sectionsChildren = new ArrayList<LinkedList<BlockItemNode>>();
				for (ASTNode child : pragmaBody.children()) {
					if (child instanceof OmpWorksharingNode) {
						if (((OmpWorksharingNode) child).ompWorkshareNodeKind()
								.toString().equals("SECTION")) {
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
						.newFunctionCallNode(
								newSource(sectionsPlace,
										CivlcTokenConstant.CALL),
								this.identifierExpression(
										newSource(sectionsPlace,
												CivlcTokenConstant.IDENTIFIER),
										"$omp_arrive_sections"),
								Arrays.asList(
										this.identifierExpression(
												newSource(
														sectionsPlace,
														CivlcTokenConstant.IDENTIFIER),
												TEAM),
										nodeFactory
												.newIntegerConstantNode(
														newSource(
																sectionsPlace,
																CivlcTokenConstant.INTEGER_CONSTANT),
														String.valueOf(this.ompArriveSections)),
										nodeFactory
												.newIntegerConstantNode(
														newSource(
																sectionsPlace,
																CivlcTokenConstant.INTEGER_CONSTANT),
														String.valueOf(numberSections))),
								null);
				this.ompArriveSections++;
				String mySecDeclaration = "my_secsDeclaration";
				VariableDeclarationNode my_secs;
				my_secs = nodeFactory
						.newVariableDeclarationNode(
								newSource(sectionsPlace,
										CivlcTokenConstant.DECLARATION),
								nodeFactory.newIdentifierNode(
										newSource(mySecDeclaration,
												CivlcTokenConstant.IDENTIFIER),
										"my_secs"),
								nodeFactory
										.newDomainTypeNode(
												newSource(
														mySecDeclaration,
														CivlcTokenConstant.DOMAIN),
												nodeFactory
														.newIntegerConstantNode(
																newSource(
																		mySecDeclaration,
																		CivlcTokenConstant.INTEGER_CONSTANT),
																"1")),
								ompArriveSections);
				items.add(my_secs);

				// Declare local copies of the private variables
				if (privateList != null) {
					for (ASTNode child : privateList.children()) {
						VariableDeclarationNode localPrivate = addPrivateVariable(
								(IdentifierExpressionNode) child, "regular");
						items.add(localPrivate);
					}
				}

				// Add firstprivate variable declarations
				if (firstPrivateIDs != null) {
					for (ASTNode child : firstPrivateIDs.children()) {
						VariableDeclarationNode firstPrivate = addPrivateVariable(
								(IdentifierExpressionNode) child, "first");
						items.add(firstPrivate);
					}
				}

				CivlForNode cfn;
				String civlFor = "civlFor";
				List<BlockItemNode> forItems = new LinkedList<>();

				// for loop;
				ForLoopInitializerNode initializerNode = nodeFactory
						.newForLoopInitializerNode(
								newSource(civlFor,
										CivlcTokenConstant.INITIALIZER_LIST),
								Arrays.asList(nodeFactory
										.newVariableDeclarationNode(
												newSource(
														civlFor,
														CivlcTokenConstant.DECLARATION),
												nodeFactory
														.newIdentifierNode(
																newSource(
																		civlFor,
																		CivlcTokenConstant.IDENTIFIER),
																"i$omp"),
												nodeFactory
														.newBasicTypeNode(
																newSource(
																		civlFor,
																		CivlcTokenConstant.INT),
																BasicTypeKind.INT))));

				StatementNode forBody;
				StatementNode switchBody;
				List<BlockItemNode> switchItems = new LinkedList<>();
				int caseNumber = 0;
				String caseItem = "caseItem";
				for (LinkedList<BlockItemNode> tempChildren : sectionsChildren) {
					StatementNode caseBody;
					List<BlockItemNode> caseItems = tempChildren;
					caseItems.add(nodeFactory.newBreakNode(newSource(caseItem,
							CivlcTokenConstant.BREAK)));
					caseBody = nodeFactory.newCompoundStatementNode(
							newSource(caseItem,
									CivlcTokenConstant.COMPOUND_STATEMENT),
							caseItems);
					SwitchLabelNode labelDecl = nodeFactory
							.newCaseLabelDeclarationNode(
									newSource(caseItem, CivlcTokenConstant.CASE),
									nodeFactory
											.newIntegerConstantNode(
													newSource(
															caseItem,
															CivlcTokenConstant.INTEGER_CONSTANT),
													String.valueOf(caseNumber)),
									caseBody);
					switchItems.add(nodeFactory.newLabeledStatementNode(
							newSource(caseItem,
									CivlcTokenConstant.CASE_LABELED_STATEMENT),
							labelDecl, caseBody));
					caseNumber++;
				}
				switchBody = nodeFactory.newCompoundStatementNode(
						newSource(civlFor,
								CivlcTokenConstant.COMPOUND_STATEMENT),
						switchItems);
				forItems.add(nodeFactory.newSwitchNode(
						newSource(civlFor, CivlcTokenConstant.SWITCH), this
								.identifierExpression(
										newSource(civlFor,
												CivlcTokenConstant.IDENTIFIER),
										"i$omp"), switchBody));
				forBody = nodeFactory.newCompoundStatementNode(
						newSource(civlFor,
								CivlcTokenConstant.COMPOUND_STATEMENT),
						forItems);

				cfn = nodeFactory.newCivlForNode(
						newSource(sectionsPlace, CivlcTokenConstant.CIVLFOR),
						false, (DeclarationListNode) initializerNode,
						nodeFactory.newIdentifierExpressionNode(
								newSource(civlFor,
										CivlcTokenConstant.IDENTIFIER),
								nodeFactory.newIdentifierNode(
										newSource(civlFor,
												CivlcTokenConstant.IDENTIFIER),
										"my_secs")), forBody, null);
				items.add(cfn);

				if (!((OmpWorksharingNode) node).nowait()) {
					items.add(barrierAndFlush(TEAM));
				}

				CompoundStatementNode sectionBody = nodeFactory
						.newCompoundStatementNode(
								newSource(sectionsPlace,
										CivlcTokenConstant.COMPOUND_STATEMENT),
								items);

				int index = node.childIndex();
				ASTNode parent = node.parent();
				parent.setChild(index, sectionBody);

				children = forBody.children();

				if (privateList != null) {
					for (ASTNode child : privateList.children()) {
						if (child != null) {
							child.remove();
							privateIDs
									.addSequenceChild((IdentifierExpressionNode) child);
						}
					}
				}

				for (ASTNode child : children) {
					replaceOMPPragmas(child, privateIDs, sharedIDs,
							reductionIDs, firstPrivateIDs, threadPrivateIDs);
				}

			}
			if (workshareKind.equals("SINGLE")) {
				SequenceNode<IdentifierExpressionNode> privateList = ((OmpWorksharingNode) node)
						.privateList();
				removeNodeFromParent(privateList);
				SequenceNode<IdentifierExpressionNode> copyPrivateList = ((OmpWorksharingNode) node)
						.copyprivateList();
				removeNodeFromParent(copyPrivateList);

				boolean removed = false;
				for (ASTNode child : sharedIDs.children()) {
					IdentifierExpressionNode idexp = (IdentifierExpressionNode) child;
					IdentifierNode id = idexp.getIdentifier();
					if (privateList != null) {
						for (ASTNode childPrivateList : privateList.children()) {
							IdentifierExpressionNode privateIdexp = (IdentifierExpressionNode) childPrivateList;
							IdentifierNode privateId = privateIdexp
									.getIdentifier();
							if (id.name().equals(privateId.name())) {
								child.remove();
								removed = true;
							}
						}
					}
					if (copyPrivateList != null) {
						for (ASTNode childPrivateList : copyPrivateList
								.children()) {
							IdentifierExpressionNode privateIdexp = (IdentifierExpressionNode) childPrivateList;
							IdentifierNode privateId = privateIdexp
									.getIdentifier();
							if (id.name().equals(privateId.name())) {
								child.remove();
								removed = true;
							}
						}
					}

				}
				SequenceNode<IdentifierExpressionNode> newSharedList;
				List<IdentifierExpressionNode> list = new LinkedList<IdentifierExpressionNode>();
				if (removed) {
					for (ASTNode child : sharedIDs.children()) {
						if (child != null) {
							child.remove();
							list.add((IdentifierExpressionNode) child);
						}
					}
					newSharedList = nodeFactory.newSequenceNode(
							newSource("sharedList",
									CivlcTokenConstant.IDENTIFIER_LIST),
							"sharedList", list);
					sharedIDs = newSharedList;
				}

				String singlePlace = "single";
				ExpressionNode arriveSingle = nodeFactory
						.newFunctionCallNode(
								newSource("arrive", CivlcTokenConstant.CALL),
								this.identifierExpression(
										newSource("arrive",
												CivlcTokenConstant.IDENTIFIER),
										"$omp_arrive_single"),
								Arrays.asList(
										this.identifierExpression(
												newSource(
														"arrive",
														CivlcTokenConstant.IDENTIFIER),
												TEAM),
										nodeFactory
												.newIntegerConstantNode(
														newSource(
																"arrive",
																CivlcTokenConstant.INTEGER_CONSTANT),
														this.ompArriveSingle
																+ "")), null);
				this.ompArriveSingle++;
				items.add(nodeFactory.newVariableDeclarationNode(
						newSource(singlePlace, CivlcTokenConstant.DECLARATION),
						nodeFactory
								.newIdentifierNode(
										newSource(singlePlace,
												CivlcTokenConstant.IDENTIFIER),
										"owner"), nodeFactory.newBasicTypeNode(
								newSource(singlePlace, CivlcTokenConstant.INT),
								BasicTypeKind.INT), arriveSingle));

				if (copyPrivateList != null) {
					for (ASTNode child : copyPrivateList.children()) {
						if (child != null) {
							VariableDeclarationNode localSharedVar;
							IdentifierNode c = (IdentifierNode) child.child(0);
							String localDeclaration = "LocalSharedVarDeclaration";
							TypeNode privateType = ((VariableDeclarationNode) ((Variable) c
									.getEntity()).getFirstDeclaration())
									.getTypeNode().copy();
							IdentifierNode localSharedIdentifer = nodeFactory
									.newIdentifierNode(
											newSource(
													c.name() + localDeclaration,
													CivlcTokenConstant.IDENTIFIER),
											OMPPRE + c.name() + "_private");
							Type currentType = ((Variable) c.getEntity())
									.getType();

							if (privateType instanceof ArrayTypeNode
									&& currentType instanceof PointerType) {
								if (!(((PointerType) currentType)
										.referencedType() instanceof ArrayType)) {
									currentType = ((PointerType) currentType)
											.referencedType();
									while (currentType instanceof ArrayType) {
										currentType = ((ArrayType) currentType)
												.getElementType();
									}
									BasicTypeKind baseTypeKind = ((StandardBasicType) currentType)
											.getBasicTypeKind();

									privateType = nodeFactory
											.newPointerTypeNode(
													newSource(
															c.name()
																	+ localDeclaration,
															CivlcTokenConstant.IDENTIFIER),
													nodeFactory
															.newBasicTypeNode(
																	newSource(
																			localDeclaration,
																			CivlcTokenConstant.TYPE),
																	baseTypeKind));
								}
							}

							ExpressionNode localCopyPrivate = this
									.identifierExpression(
											newSource(
													c.name() + localDeclaration,
													CivlcTokenConstant.IDENTIFIER),
											c.name());

							localSharedVar = nodeFactory
									.newVariableDeclarationNode(
											newSource(
													localDeclaration,
													CivlcTokenConstant.DECLARATION),
											localSharedIdentifer, privateType,
											localCopyPrivate);
							items.add(localSharedVar);
						}
					}
				}

				List<ExpressionNode> operands = new ArrayList<ExpressionNode>();
				operands.add(this.identifierExpression(
						newSource(singlePlace, CivlcTokenConstant.IDENTIFIER),
						"owner"));
				operands.add(this.identifierExpression(
						newSource(singlePlace, CivlcTokenConstant.IDENTIFIER),
						TID));

				CompoundStatementNode ifBody;
				LinkedList<BlockItemNode> ifItems = new LinkedList<>();

				// Declare local copies of the private variables
				if (privateList != null) {
					for (ASTNode child : privateList.children()) {
						VariableDeclarationNode localPrivate = addPrivateVariable(
								(IdentifierExpressionNode) child, "regular");
						ifItems.add(localPrivate);
					}
				}

				int i = 0;
				for (ASTNode child : node.children()) {
					node.removeChild(i);
					ifItems.add((BlockItemNode) child);
					i++;
				}
				ifBody = nodeFactory
						.newCompoundStatementNode(
								newSource(singlePlace,
										CivlcTokenConstant.COMPOUND_STATEMENT),
								ifItems);

				if (copyPrivateList != null) {
					for (ASTNode child : copyPrivateList.children()) {
						IdentifierNode c = ((IdentifierExpressionNode) child)
								.getIdentifier();

						ExpressionNode expression = nodeFactory
								.newOperatorNode(
										newSource("copyPrivate",
												CivlcTokenConstant.EXPR),
										Operator.ASSIGN,
										Arrays.asList(
												this.identifierExpression(
														newSource(
																"copyPrivate",
																CivlcTokenConstant.IDENTIFIER),
														c.name()),
												this.identifierExpression(
														newSource(
																"copyPrivate",
																CivlcTokenConstant.IDENTIFIER),
														OMPPRE + c.name()
																+ "_private")));
						ExpressionStatementNode statement = nodeFactory
								.newExpressionStatementNode(expression);

						int ifChildren = ifBody.numChildren();
						ASTNode lastChild = ifBody.child(ifChildren - 1);

						Pair<VariableDeclarationNode, ExpressionStatementNode> tempPair = new Pair<>(
								null, statement);
						if (sharedWrite.containsKey(lastChild)) {
							ArrayList<Pair<VariableDeclarationNode, ExpressionStatementNode>> nodeToAdd = sharedRead
									.get(lastChild);
							nodeToAdd.add(tempPair);
						} else {
							ArrayList<Pair<VariableDeclarationNode, ExpressionStatementNode>> tempPairs = new ArrayList<Pair<VariableDeclarationNode, ExpressionStatementNode>>();
							tempPairs.add(tempPair);
							sharedWrite.put(lastChild, tempPairs);
						}

					}
				}

				IfNode ifStatement = nodeFactory.newIfNode(
						newSource(singlePlace, CivlcTokenConstant.IF),
						nodeFactory.newOperatorNode(
								newSource(singlePlace,
										CivlcTokenConstant.EQUALS),
								Operator.EQUALS, operands), ifBody);
				items.add(ifStatement);
				items.add(barrierAndFlush(TEAM));
				body = nodeFactory.newCompoundStatementNode(
						newSource(singlePlace,
								CivlcTokenConstant.COMPOUND_STATEMENT), items);

				int index = node.childIndex();
				ASTNode parent = node.parent();
				parent.setChild(index, body);

				children = ifBody.children();

				if (privateList != null) {
					for (ASTNode child : privateList.children()) {
						if (child != null) {
							child.remove();
							privateIDs
									.addSequenceChild((IdentifierExpressionNode) child);
						}
					}
				}

				if (copyPrivateList != null) {
					for (ASTNode child : copyPrivateList.children()) {
						if (child != null) {
							child.remove();
							privateIDs
									.addSequenceChild((IdentifierExpressionNode) child);
						}
					}
				}

				for (ASTNode child : children) {
					replaceOMPPragmas(child, privateIDs, sharedIDs,
							reductionIDs, firstPrivateIDs, threadPrivateIDs);
				}

			}
		} else if (node instanceof FunctionCallNode) {
			boolean replaced = replaceOmpFunction((FunctionCallNode) node);
			if (!replaced) {
				for (ASTNode child : node.children()) {
					replaceOMPPragmas(child, privateIDs, sharedIDs,
							reductionIDs, firstPrivateIDs, threadPrivateIDs);
				}
			}
		} else if (node instanceof IdentifierNode) {
			if (privateIDs != null) {
				for (ASTNode child : privateIDs.children()) {
					IdentifierNode c = ((IdentifierExpressionNode) child)
							.getIdentifier();
					if (c.name().equals(((IdentifierNode) node).name())) {
						((IdentifierNode) node).setName(OMPPRE
								+ ((IdentifierNode) node).name() + "_private");
					}
				}
			}
			if (firstPrivateIDs != null) {
				for (ASTNode child : firstPrivateIDs.children()) {
					IdentifierNode c = ((IdentifierExpressionNode) child)
							.getIdentifier();
					if (c.name().equals(((IdentifierNode) node).name())) {
						((IdentifierNode) node).setName(OMPPRE
								+ ((IdentifierNode) node).name() + "_private");
					}
				}
			}
			if (reductionIDs != null) {
				for (ASTNode child : reductionIDs.children()) {
					IdentifierNode c = ((IdentifierExpressionNode) child)
							.getIdentifier();
					if (c.name().equals(((IdentifierNode) node).name())) {
						((IdentifierNode) node)
								.setName(OMPPRE
										+ ((IdentifierNode) node).name()
										+ "_reduction");
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
									(BlockItemNode) parent, privateIDs,
									sharedIDs, reductionIDs, firstPrivateIDs);
						}

					}
				}
			}
			if (threadPrivateIDs != null) {
				for (ASTNode child : threadPrivateIDs.children()) {
					IdentifierNode c = ((IdentifierExpressionNode) child)
							.getIdentifier();
					if (c.name().equals(((IdentifierNode) node).name())) {
						ASTNode idExp = node.parent();
						IdentifierExpressionNode arg0 = (IdentifierExpressionNode) this
								.identifierExpression(
										newSource("threadPrivate",
												CivlcTokenConstant.IDENTIFIER),
										c.name() + "$omp_threadprivate");
						IdentifierExpressionNode arg1 = (IdentifierExpressionNode) this
								.identifierExpression(
										newSource("threadPrivate",
												CivlcTokenConstant.IDENTIFIER),
										TID);

						OperatorNode threadPrivateReplace = nodeFactory
								.newOperatorNode(
										newSource("threadPrivate",
												CivlcTokenConstant.EXPR),
										Operator.SUBSCRIPT, arg0, arg1);

						int index = idExp.childIndex();
						ASTNode parent = idExp.parent();
						parent.setChild(index, threadPrivateReplace);

					}
				}
			}

		} else if (node instanceof OperatorNode
				&& sharedIDs != null
				&& isAssignmentOperator(((OperatorNode) node).getOperator()
						.toString()) != 0) {

			int op = isAssignmentOperator(((OperatorNode) node).getOperator()
					.toString());
			if (op != 0) {
				ASTNode lhs = node.child(0);
				while (!(lhs instanceof IdentifierNode)) {
					lhs = lhs.child(0);
				}

				for (ASTNode child : sharedIDs.children()) {
					IdentifierNode c = ((IdentifierExpressionNode) child)
							.getIdentifier();
					if (c.name().equals(((IdentifierNode) lhs).name())) {
						boolean isInReduction = false;
						if (reductionIDs != null) {
							for (ASTNode childReduction : reductionIDs
									.children()) {
								IdentifierNode cReduction = ((IdentifierExpressionNode) childReduction)
										.getIdentifier();
								if (cReduction.name().equals(
										((IdentifierNode) lhs).name())) {
									isInReduction = true;
								}
							}
						}
						if (!isInReduction) {
							sharedWrite((IdentifierNode) lhs, privateIDs,
									sharedIDs, reductionIDs, firstPrivateIDs,
									threadPrivateIDs, op);
						}
					}
				}

				for (int i = 0; i < node.numChildren(); i++) {
					ASTNode child = node.child(i);
					replaceOMPPragmas(child, privateIDs, sharedIDs,
							reductionIDs, firstPrivateIDs, threadPrivateIDs);
				}
			}

		} else if (node instanceof OperatorNode) {
			for (int i = node.numChildren() - 1; i >= 0; i--) {
				replaceOMPPragmas(node.child(i), privateIDs, sharedIDs,
						reductionIDs, firstPrivateIDs, threadPrivateIDs);
			}
		} else if (node instanceof ForLoopNode && sharedIDs != null) {
			ASTNode oldBody;
			CompoundStatementNode whileBody;
			LinkedList<BlockItemNode> items = new LinkedList<BlockItemNode>();
			ExpressionNode incrementer = ((ForLoopNode) node).getIncrementer();
			ExpressionNode condition = ((ForLoopNode) node).getCondition();
			ForLoopInitializerNode initializer = ((ForLoopNode) node)
					.getInitializer();
			String forToWhile = "forToWhileTransforamtion";
			boolean found = containsSharedVar(incrementer, sharedIDs);
			found = found || containsSharedVar(condition, sharedIDs);
			found = found || containsSharedVar(initializer, sharedIDs);

			if (found) {
				condition.remove();
				incrementer.remove();
				initializer.remove();

				oldBody = ((ForLoopNode) node).getBody();
				if (oldBody instanceof CompoundStatementNode) {
					for (ASTNode child : oldBody.children()) {
						child.remove();
						items.add((BlockItemNode) child);
					}
				} else {
					oldBody.remove();
					items.add((BlockItemNode) oldBody);
				}

				if (((OperatorNode) incrementer).getOperator() == Operator.COMMA) {
					OperatorNode op = (OperatorNode) incrementer;
					boolean added = false;
					while (op.getOperator() == Operator.COMMA && !added) {
						OperatorNode arg1 = (OperatorNode) op.getArgument(0);
						OperatorNode arg2 = (OperatorNode) op.getArgument(1);
						if (arg1.getOperator() != Operator.COMMA) {
							arg1.remove();
							items.add(nodeFactory
									.newExpressionStatementNode(arg1));
							added = true;
						} else {
							op = arg1;
						}
						if (arg2.getOperator() != Operator.COMMA) {
							arg2.remove();
							items.add(nodeFactory
									.newExpressionStatementNode(arg2));
							added = added && true;
						} else {
							op = arg2;
						}
					}
				} else {
					items.add(nodeFactory
							.newExpressionStatementNode(incrementer));
				}

				whileBody = nodeFactory.newCompoundStatementNode(
						newSource(forToWhile,
								CivlcTokenConstant.COMPOUND_STATEMENT), items);

				LoopNode whileNode = nodeFactory.newWhileLoopNode(
						newSource("forToWhile", CivlcTokenConstant.WHILE),
						condition, whileBody, null);

				LinkedList<ExpressionStatementNode> initializers = new LinkedList<ExpressionStatementNode>();
				if (((OperatorNode) initializer).getOperator() == Operator.COMMA) {
					OperatorNode op = (OperatorNode) initializer;
					boolean added = false;
					while (op.getOperator() == Operator.COMMA && !added) {
						OperatorNode arg1 = (OperatorNode) op.getArgument(0);
						OperatorNode arg2 = (OperatorNode) op.getArgument(1);
						if (arg1.getOperator() != Operator.COMMA) {
							arg1.remove();
							initializers.add(nodeFactory
									.newExpressionStatementNode(arg1));
							added = true;
						} else {
							op = arg1;
						}
						if (arg2.getOperator() != Operator.COMMA) {
							arg2.remove();
							initializers.add(nodeFactory
									.newExpressionStatementNode(arg2));
							added = added && true;
						} else {
							op = arg2;
						}
					}
				} else {
					initializers
							.add(nodeFactory
									.newExpressionStatementNode((ExpressionNode) initializer));
				}

				CompoundStatementNode body;
				LinkedList<BlockItemNode> forReplace = new LinkedList<BlockItemNode>();

				for (ExpressionStatementNode child : initializers) {
					forReplace.add(child);
				}

				forReplace.add(whileNode);
				body = nodeFactory.newCompoundStatementNode(
						newSource(forToWhile,
								CivlcTokenConstant.COMPOUND_STATEMENT),
						forReplace);

				int index = node.childIndex();
				ASTNode parent = node.parent();
				parent.setChild(index, body);

				Iterable<ASTNode> children = body.children();
				for (ASTNode child : children) {
					replaceOMPPragmas(child, privateIDs, sharedIDs,
							reductionIDs, firstPrivateIDs, threadPrivateIDs);
				}
			} else {
				Iterable<ASTNode> children = node.children();
				for (ASTNode child : children) {
					replaceOMPPragmas(child, privateIDs, sharedIDs,
							reductionIDs, firstPrivateIDs, threadPrivateIDs);
				}
			}

		} else if (node instanceof OmpDeclarativeNode) {
			// Create array of threadprivate vars for each var
			SequenceNode<IdentifierExpressionNode> vars = ((OmpDeclarativeNode) node)
					.variables();
			vars.remove();
			for (ASTNode child : vars.children()) {
				String c = ((IdentifierExpressionNode) child).getIdentifier()
						.name();
				IdentifierNode name = nodeFactory.newIdentifierNode(
						newSource("threadPrivate",
								CivlcTokenConstant.IDENTIFIER), c
								+ "$omp_threadprivate");
				IdentifierNode id = ((IdentifierExpressionNode) child)
						.getIdentifier();
				TypeNode privateType = ((VariableDeclarationNode) ((Variable) id
						.getEntity()).getFirstDeclaration()).getTypeNode()
						.copy();
				IdentifierExpressionNode extent = (IdentifierExpressionNode) this
						.identifierExpression(
								newSource("threadPrivate",
										CivlcTokenConstant.IDENTIFIER), OMPPRE
										+ "num_threads");
				ArrayTypeNode arrayType = nodeFactory.newArrayTypeNode(
						newSource("threadPrivate", CivlcTokenConstant.TYPE),
						privateType, extent);
				VariableDeclarationNode arrayNode = nodeFactory
						.newVariableDeclarationNode(
								newSource("threadPrivate",
										CivlcTokenConstant.DECLARATION), name,
								arrayType);
				int index = node.childIndex();
				ASTNode parent = node.parent();

				ASTNode nextNode = parent.child(index + 1);

				// Insert new nodes
				Pair<VariableDeclarationNode, ExpressionStatementNode> tempPair = new Pair<>(
						arrayNode, null);
				if (sharedWrite.containsKey(nextNode)) {
					ArrayList<Pair<VariableDeclarationNode, ExpressionStatementNode>> nodeToAdd = sharedWrite
							.get(nextNode);
					nodeToAdd.add(tempPair);
				} else {
					ArrayList<Pair<VariableDeclarationNode, ExpressionStatementNode>> tempPairs = new ArrayList<Pair<VariableDeclarationNode, ExpressionStatementNode>>();
					tempPairs.add(tempPair);
					sharedWrite.put(nextNode, tempPairs);
				}
				threadPrivateIDs
						.addSequenceChild((IdentifierExpressionNode) child
								.copy());
			}

			// Remove old node
			node.remove();

		} else if (node != null) {
			Iterable<ASTNode> children = node.children();
			for (ASTNode child : children) {
				replaceOMPPragmas(child, privateIDs, sharedIDs, reductionIDs,
						firstPrivateIDs, threadPrivateIDs);
			}
		}

	}

	/**
	 * Check if the current node contains a shared variable.
	 * 
	 * @param node
	 * @param sharedIDs
	 * @return If there is a shared variable in the node, return true.
	 */
	private boolean containsSharedVar(ASTNode node,
			SequenceNode<IdentifierExpressionNode> sharedIDs) {
		if (node instanceof IdentifierNode) {
			for (ASTNode child : sharedIDs.children()) {
				IdentifierNode c = ((IdentifierExpressionNode) child)
						.getIdentifier();
				if (c.name().equals(((IdentifierNode) node).name())) {
					return true;
				}
			}
		} else if (node != null) {
			Iterable<ASTNode> children = node.children();
			boolean found = false;
			for (ASTNode child : children) {
				return found || containsSharedVar(child, sharedIDs);
			}
		}
		return false;
	}

	/**
	 * Get the temp variable for a node. This method will generate a temp
	 * variable that is used in the omp_read or omp_write functions.
	 * 
	 * @param node
	 * @param readWrite
	 * @param count
	 * @return
	 */
	private Pair<VariableDeclarationNode, Integer> getTempVar(
			IdentifierNode node, String readWrite, int count) {
		VariableDeclarationNode temp;
		Type currentType = ((Variable) node.getEntity()).getType();
		int nodesDeep = 0;
		boolean pointer = false;
		while (currentType instanceof PointerType) {
			currentType = ((PointerType) currentType).referencedType();
			nodesDeep++;
			pointer = true;
		}

		if (currentType instanceof QualifiedObjectType) {
			currentType = ((QualifiedObjectType) currentType).getBaseType();
		}

		while (currentType instanceof ArrayType) {
			currentType = ((ArrayType) currentType).getElementType();
			nodesDeep++;
		}
		String place = node.name() + "Shared" + readWrite;

		BasicTypeKind baseTypeKind = null;
		if (currentType instanceof StandardBasicType) {
			baseTypeKind = ((StandardBasicType) currentType).getBasicTypeKind();
		}

		IdentifierNode tempID = nodeFactory.newIdentifierNode(
				newSource(place, CivlcTokenConstant.IDENTIFIER), OMPPRE
						+ readWrite + String.valueOf(count));
		TypeNode declarationTypeNode = null;

		boolean parentIsFunctionCall = false;
		if (pointer) {
			parentIsFunctionCall = checkIfParentIsFunction(node);
		}

		boolean tempBool = true;

		if (currentType instanceof StructureOrUnionType) {
			StructureOrUnionTypeNode stn = (StructureOrUnionTypeNode) ((StructureOrUnionType) currentType)
					.getKey();
			StructureOrUnionTypeNode copy = stn.copy();
			copy.getStructDeclList().remove();
			declarationTypeNode = copy;
			tempBool = false;
			nodesDeep = 0;
		}

		if (parentIsFunctionCall && tempBool) {
			declarationTypeNode = nodeFactory.newPointerTypeNode(
					newSource(place, CivlcTokenConstant.TYPE), nodeFactory
							.newBasicTypeNode(
									newSource(place, CivlcTokenConstant.TYPE),
									baseTypeKind));
			nodesDeep--;
			while (nodesDeep > 0) {
				declarationTypeNode = nodeFactory.newPointerTypeNode(
						newSource(place, CivlcTokenConstant.POINTER),
						declarationTypeNode);
				nodesDeep--;
			}
		} else if (tempBool) {
			declarationTypeNode = nodeFactory.newBasicTypeNode(
					newSource(place, CivlcTokenConstant.TYPE), baseTypeKind);
		}

		temp = nodeFactory.newVariableDeclarationNode(
				newSource(place, CivlcTokenConstant.DECLARATION), tempID,
				declarationTypeNode);

		Pair<VariableDeclarationNode, Integer> pair = new Pair<>(temp,
				nodesDeep);

		return pair;
	}

	/**
	 * Method to transform a shared write in C to CIVL-C
	 * 
	 * @param node
	 * @param privateIDs
	 * @param sharedIDs
	 * @param reductionIDs
	 * @param firstPrivateIDs
	 * @param threadPrivateIDs
	 * @param opCode
	 * @throws SyntaxException
	 * @throws NoSuchElementException
	 */
	private void sharedWrite(IdentifierNode node,
			SequenceNode<IdentifierExpressionNode> privateIDs,
			SequenceNode<IdentifierExpressionNode> sharedIDs,
			SequenceNode<IdentifierExpressionNode> reductionIDs,
			SequenceNode<IdentifierExpressionNode> firstPrivateIDs,
			SequenceNode<IdentifierExpressionNode> threadPrivateIDs, int opCode)
			throws SyntaxException, NoSuchElementException {
		VariableDeclarationNode temp;
		Type currentType = ((Variable) node.getEntity()).getType();
		int nodesDeep = 0;
		Type origType = currentType;
		String place = node.name() + "SharedWrite";

		Pair<VariableDeclarationNode, Integer> pair = getTempVar(node, "write",
				tempWriteCount);

		temp = pair.left;
		nodesDeep = pair.right;

		ASTNode parentOfID = null;
		String nodeName = node.name();
		node.setName(OMPPRE + node.name() + "_local");
		ExpressionStatementNode writeCall = null;
		ExpressionStatementNode readCall = null;
		ASTNode statementParent = node.parent();

		// Get the parent of the identifer that is a StatementNode
		while (!(statementParent instanceof StatementNode)) {
			statementParent = statementParent.parent();
		}
		if (nodesDeep == 0) {
			parentOfID = node.parent();
			writeCall = write((ExpressionNode) parentOfID.copy(), nodeName,
					this.identifierExpression(
							newSource(place, CivlcTokenConstant.IDENTIFIER),
							OMPPRE + "write" + String.valueOf(tempWriteCount)),
					origType);
			if (opCode == 2) {
				readCall = read((ExpressionNode) parentOfID.copy(), nodeName,
						OMPPRE + "write" + String.valueOf(tempWriteCount),
						origType);
			}
		} else {
			parentOfID = node.parent();
			while (nodesDeep > 0) {
				parentOfID = parentOfID.parent();
				nodesDeep--;
			}
			if (parentOfID instanceof OperatorNode) {
				checkArrayIndices((OperatorNode) parentOfID, privateIDs,
						sharedIDs, reductionIDs, firstPrivateIDs,
						threadPrivateIDs);
			}

			writeCall = write((ExpressionNode) parentOfID.copy(), nodeName,
					this.identifierExpression(
							newSource(place, CivlcTokenConstant.IDENTIFIER),
							OMPPRE + "write" + String.valueOf(tempWriteCount)),
					origType);
			if (opCode == 2) {
				readCall = read((ExpressionNode) parentOfID.copy(), nodeName,
						OMPPRE + "write" + String.valueOf(tempWriteCount),
						origType);
			}
		}

		ASTNode parent = parentOfID.parent();
		int index = parentOfID.childIndex();
		parent.setChild(
				index,
				this.identifierExpression(OMPPRE + "write"
						+ String.valueOf(tempWriteCount)));

		if (opCode == 2) {
			recordSharedReadWrite("read", null, readCall, statementParent);
		}

		recordSharedReadWrite("write", temp, writeCall, statementParent);

		tempWriteCount++;
	}

	/**
	 * Record shared read and write statements so that the omp_read and
	 * omp_write statements can be inserted.
	 * 
	 * @param readWrite
	 * @param decl
	 * @param statement
	 * @param statementParent
	 */
	private void recordSharedReadWrite(String readWrite,
			VariableDeclarationNode decl, ExpressionStatementNode statement,
			ASTNode statementParent) {
		Pair<VariableDeclarationNode, ExpressionStatementNode> pair = new Pair<>(
				decl, statement);

		if (readWrite.equals("write")) {
			if (sharedWrite.containsKey(statementParent)) {
				ArrayList<Pair<VariableDeclarationNode, ExpressionStatementNode>> nodeToAdd = sharedWrite
						.get(statementParent);
				nodeToAdd.add(pair);
			} else {
				ArrayList<Pair<VariableDeclarationNode, ExpressionStatementNode>> pairs = new ArrayList<Pair<VariableDeclarationNode, ExpressionStatementNode>>();
				pairs.add(pair);
				sharedWrite.put(statementParent, pairs);
			}
		} else {
			if (sharedRead.containsKey(statementParent)) {
				ArrayList<Pair<VariableDeclarationNode, ExpressionStatementNode>> nodeToAdd = sharedRead
						.get(statementParent);
				nodeToAdd.add(pair);
			} else {
				ArrayList<Pair<VariableDeclarationNode, ExpressionStatementNode>> pairs = new ArrayList<Pair<VariableDeclarationNode, ExpressionStatementNode>>();
				pairs.add(pair);
				sharedRead.put(statementParent, pairs);
			}

		}
	}

	/**
	 * If the node like a for or if and more than one statement added then a
	 * body needs to be created for the for or if node
	 * 
	 * @param node
	 */
	private void createBody(ASTNode node) {
		int index = node.childIndex();
		ASTNode parent = node.parent();
		CompoundStatementNode body;
		LinkedList<BlockItemNode> items = new LinkedList<>();

		parent.removeChild(index);
		items.add((BlockItemNode) node);
		body = nodeFactory.newCompoundStatementNode(
				newSource("ForBody", CivlcTokenConstant.COMPOUND_STATEMENT),
				items);
		parent.setChild(index, body);
	}

	/**
	 * Insert a nodeToInsert in position k of the parent.
	 * 
	 * @param k
	 * @param parent
	 * @param nodeToInsert
	 */
	private void insertChildAt(int k, ASTNode parent, ASTNode nodeToInsert) {
		int numChildren = parent.numChildren();

		if (k >= numChildren) {
			parent.setChild(k, nodeToInsert);
		} else {
			ASTNode current = parent.removeChild(k);
			ASTNode next = null;
			parent.setChild(k, nodeToInsert);
			if (current != null) {
				for (int i = k + 1; i <= numChildren; i++) {
					if (i == numChildren) {
						parent.setChild(i, current);
						break;
					}
					next = parent.child(i);
					if (next != null) {
						parent.removeChild(i);
						parent.setChild(i, current);
					} else {
						parent.setChild(i, current);
						break;
					}
					current = next;

				}
			}
		}

	}

	/**
	 * Take a node that is a FunctionCallNode of some OpenMP function and
	 * replace it with an equivalent function that is a CIVL-C function
	 * 
	 * @param node
	 * @return
	 * @throws SyntaxException
	 */
	private boolean replaceOmpFunction(FunctionCallNode node)
			throws SyntaxException {
		ExpressionNode function = node.getFunction();
		String functionName = null;
		if (function instanceof IdentifierExpressionNode) {
			functionName = ((IdentifierExpressionNode) function)
					.getIdentifier().name();
		}
		ASTNode replacementNode = null;
		String place;
		if (functionName != null) {
			switch (functionName) {
			case "omp_get_num_threads":
				place = "omp_get_num_threads->" + OMPPRE + "nthreads";
				replacementNode = this.identifierExpression(
						newSource(place, CivlcTokenConstant.IDENTIFIER),
						NTHREADS);
				break;
			case "omp_get_num_procs":
				place = "omp_get_num_procs->1";
				replacementNode = nodeFactory.newIntegerConstantNode(
						(newSource(place, CivlcTokenConstant.IDENTIFIER)), "1");
				break;
			case "omp_get_max_threads":
				place = "omp_get_max_threads->" + OMPPRE + "nthreads";
				replacementNode = this.identifierExpression(
						newSource(place, CivlcTokenConstant.IDENTIFIER),
						THREADMAX);
				break;
			case "omp_get_thread_num":
				place = "omp_get_thread_num->" + TID;
				replacementNode = this.identifierExpression(
						newSource(place, CivlcTokenConstant.IDENTIFIER), TID);
				break;
			case "omp_set_num_threads":
				place = "omp_set_num_threads->" + OMPPRE + "num_threads";
				replacementNode = nodeFactory.newOperatorNode(
						newSource(place, CivlcTokenConstant.EXPR),
						Operator.ASSIGN, Arrays.asList(this
								.identifierExpression(
										newSource(place,
												CivlcTokenConstant.IDENTIFIER),
										OMPPRE + "num_threads"), node
								.getArgument(0).copy()));
				break;
			}
		}

		if (replacementNode != null) {
			ASTNode parent = node.parent();
			int index = node.childIndex();
			parent.setChild(index, replacementNode);
			return true;
		}

		return false;
	}

	/**
	 * Check the operator and return an int for which operator it is TODO add
	 * more operators as needed
	 * 
	 * @param operator
	 * @return
	 */
	private int isAssignmentOperator(String operator) {
		if (operator.equals("ASSIGN")) {
			return 1;
		} else if (operator.equals("PLUSEQ")) {
			return 2;
		}
		return 0;
	}

	/**
	 * Create a declaration for each private variable inside a parallel node
	 * 
	 * @param node
	 * @param privateKind
	 * @return
	 * @throws SyntaxException
	 */
	private VariableDeclarationNode addPrivateVariable(
			IdentifierExpressionNode node, String privateKind)
			throws SyntaxException {
		VariableDeclarationNode privateVariable;

		IdentifierNode c = node.getIdentifier();
		String place = c.name() + "$omp_privateDeclaration";
		TypeNode privateType = ((VariableDeclarationNode) ((Variable) c
				.getEntity()).getFirstDeclaration()).getTypeNode().copy();
		IdentifierNode privateIdentifer;
		if (privateKind.equals("first")) {
			privateIdentifer = nodeFactory.newIdentifierNode(
					newSource(place, CivlcTokenConstant.IDENTIFIER),
					OMPPRE + c.name() + "_private");
			privateVariable = nodeFactory.newVariableDeclarationNode(
					newSource(place, CivlcTokenConstant.DECLARATION),
					privateIdentifer,
					privateType,
					this.identifierExpression(
							newSource(place, CivlcTokenConstant.IDENTIFIER),
							c.name()));
		} else if (privateKind.equals("reduction")) {
			privateIdentifer = nodeFactory.newIdentifierNode(
					newSource(place, CivlcTokenConstant.IDENTIFIER),
					OMPPRE + c.name() + "_reduction");
			privateVariable = nodeFactory.newVariableDeclarationNode(
					newSource(place, CivlcTokenConstant.DECLARATION),
					privateIdentifer, privateType,
					nodeFactory.newIntegerConstantNode(
							newSource(place,
									CivlcTokenConstant.INTEGER_CONSTANT), "0"));
		} else {
			privateIdentifer = nodeFactory.newIdentifierNode(
					newSource(place, CivlcTokenConstant.IDENTIFIER),
					OMPPRE + c.name() + "_private");
			privateVariable = nodeFactory.newVariableDeclarationNode(
					newSource(place, CivlcTokenConstant.DECLARATION),
					privateIdentifer, privateType);
		}
		return privateVariable;
	}

	/**
	 * Method to get a statement that is the parent of some identifier
	 * 
	 * @param node
	 * @return Node that is the parent of the IdentiferNode
	 */
	private ASTNode getParentOfID(IdentifierNode node) {
		ASTNode parent = node.parent();
		while (!(parent instanceof StatementNode || parent instanceof VariableDeclarationNode)) {
			parent = parent.parent();
		}
		return parent;
	}

	private boolean checkIfParentIsFunction(IdentifierNode node) {
		boolean parentFunction = false;
		ASTNode parent = node.parent();

		while (!(parent instanceof StatementNode)) {
			if (parent instanceof FunctionCallNode) {
				parentFunction = true;
			}
			parent = parent.parent();
		}

		return parentFunction;
	}

	private void removeNodeFromParent(ASTNode node) {
		if (node != null) {
			int index = node.childIndex();
			ASTNode parent = node.parent();
			parent.removeChild(index);
		}

	}

	/**
	 * Transform shared read from C to CIVL-C
	 * 
	 * @param node
	 * @param parentStatement
	 * @param privateIDs
	 * @param sharedIDs
	 * @param reductionIDs
	 * @param firstPrivateIDs
	 * @throws SyntaxException
	 * @throws NoSuchElementException
	 */
	private void sharedRead(IdentifierNode node, BlockItemNode parentStatement,
			SequenceNode<IdentifierExpressionNode> privateIDs,
			SequenceNode<IdentifierExpressionNode> sharedIDs,
			SequenceNode<IdentifierExpressionNode> reductionIDs,
			SequenceNode<IdentifierExpressionNode> firstPrivateIDs)
			throws SyntaxException, NoSuchElementException {

		boolean alreadyUsed = false;
		boolean write = false;
		boolean updateRead = false;
		ExpressionStatementNode writeCall = null;
		ASTNode statementParent = null;
		ASTNode parentOfID = null;

		Type currentType = ((Variable) node.getEntity()).getType();
		int nodesDeep = 0;
		VariableDeclarationNode temp;
		Type origType = currentType;

		String place = node.name() + "SharedRead";
		Pair<VariableDeclarationNode, Integer> pair = getTempVar(node, "read",
				tmpCount);

		temp = pair.left;
		nodesDeep = pair.right;

		String nodeName = null;
		for (Triple<BlockItemNode, IdentifierNode, String> triple : tempVars) {
			if (triple.second.name().equals(OMPPRE + node.name() + "_local")) {
				ASTNode parent = node.parent();
				while (parent != null) {
					if (parent.equals(triple.first)
							&& parentStatement.equals(triple.first)) {
						nodeName = node.name();

						if (nodesDeep == 0) {
							parentOfID = node.parent();
						} else {
							parentOfID = node.parent();
							while (nodesDeep > 0) {
								parentOfID = parentOfID.parent();
								nodesDeep--;
							}
						}
						int index = parentOfID.childIndex();
						ASTNode directParent = parentOfID.parent();
						alreadyUsed = true;
						statementParent = node.parent();
						while (!(statementParent instanceof StatementNode || statementParent instanceof VariableDeclarationNode)) {
							if (statementParent instanceof OperatorNode) {
								if (((OperatorNode) statementParent)
										.getOperator() == Operator.POSTDECREMENT
										|| ((OperatorNode) statementParent)
												.getOperator() == Operator.POSTINCREMENT) {
									write = true;
								}

							}
							statementParent = statementParent.parent();
						}

						writeCall = write(
								this.identifierExpression(
										newSource(place,
												CivlcTokenConstant.IDENTIFIER),
										triple.second.name()), nodeName,
								this.identifierExpression(
										newSource(place,
												CivlcTokenConstant.IDENTIFIER),
										triple.third), origType);
						directParent.setChild(index, this
								.identifierExpression(
										newSource(place,
												CivlcTokenConstant.IDENTIFIER),
										triple.third));

						break;
					}
					parent = parent.parent();
				}
			}
		}

		if (!alreadyUsed) {
			statementParent = node.parent();
			while (!(statementParent instanceof StatementNode || statementParent instanceof VariableDeclarationNode)) {
				if (statementParent instanceof OperatorNode) {
					if (((OperatorNode) statementParent).getOperator() == Operator.POSTDECREMENT
							|| ((OperatorNode) statementParent).getOperator() == Operator.POSTINCREMENT) {
						write = true;
						updateRead = true;
					}

				}
				statementParent = statementParent.parent();
			}

			nodeName = node.name();
			node.setName(OMPPRE + node.name() + "_local");
			ExpressionStatementNode readCall = null;
			statementParent = node.parent();
			while (!(statementParent instanceof StatementNode || statementParent instanceof VariableDeclarationNode)) {
				statementParent = statementParent.parent();
			}
			if (nodesDeep == 0) {
				parentOfID = node.parent();
				readCall = read((ExpressionNode) parentOfID.copy(), nodeName,
						OMPPRE + "read" + String.valueOf(tmpCount), origType);
			} else {
				parentOfID = node.parent();
				while (nodesDeep > 0) {
					if (!(parentOfID.parent() instanceof IfNode)) {
						parentOfID = parentOfID.parent();
					}
					nodesDeep--;
				}

				readCall = read((ExpressionNode) parentOfID.copy(), nodeName,
						OMPPRE + "read" + String.valueOf(tmpCount), origType);
			}

			Triple<BlockItemNode, IdentifierNode, String> tempName = new Triple<>(
					parentStatement, node, OMPPRE + "read"
							+ String.valueOf(tmpCount));
			tempVars.add(tempName);

			ASTNode parent = parentOfID.parent();
			int index = parentOfID.childIndex();
			parent.setChild(
					index,
					this.identifierExpression(OMPPRE + "read"
							+ String.valueOf(tmpCount)));

			if (statementParent instanceof LoopNode
					&& ((LoopNode) statementParent).getKind().name()
							.equals("WHILE")) {
				lastLoopVar = tmpCount;
			}

			recordSharedReadWrite("read", temp, readCall, statementParent);

			writeCall = write((ExpressionNode) parentOfID.copy(), nodeName,
					this.identifierExpression(
							newSource(place, CivlcTokenConstant.IDENTIFIER),
							OMPPRE + "read" + String.valueOf(tmpCount)),
					origType);

			tmpCount++;
		}

		if (write) {
			recordSharedReadWrite("write", null, writeCall, statementParent);

			if (updateRead && lastLoopVar != -1) {
				ExpressionStatementNode updateCall = read(
						(ExpressionNode) parentOfID.copy(), nodeName, OMPPRE
								+ "read" + String.valueOf(lastLoopVar),
						origType);
				recordSharedReadWrite("write", null, updateCall,
						statementParent);
				lastLoopVar = -1;
			}
		}

	}

	private void getLoopVariables(ASTNode node,
			ArrayList<String> alreadyDeclVars,
			SequenceNode<IdentifierExpressionNode> privateIDs) {
		for (ASTNode child : node.children()) {
			if (child != null) {
				if (child instanceof OmpForNode) {
					StatementNode forLoopNode = ((OmpExecutableNode) child)
							.statementNode();
					if (forLoopNode instanceof ForLoopNode) {
						ForLoopInitializerNode flin = ((ForLoopNode) forLoopNode)
								.getInitializer();
						if (flin instanceof OperatorNode) {
							getInitializerName((OperatorNode) flin,
									alreadyDeclVars, privateIDs);
						} else if (flin instanceof DeclarationListNode) {
							getInitializerName((DeclarationListNode) flin,
									alreadyDeclVars);
						}
					}
				}
				getLoopVariables(child, alreadyDeclVars, privateIDs);
			}
		}
	}

	private void getInitializerName(OperatorNode node,
			ArrayList<String> alreadyDeclVars,
			SequenceNode<IdentifierExpressionNode> privateIDs) {
		if (node.getOperator().toString().equals("ASSIGN")) {
			IdentifierExpressionNode name = (IdentifierExpressionNode) node
					.getArgument(0);
			String strName = name.getIdentifier().name();
			if (!(alreadyDeclVars.contains(strName))) {
				alreadyDeclVars.add(strName);
				Entity entity = ((IdentifierExpressionNode) name)
						.getIdentifier().getEntity();
				IdentifierExpressionNode newNode = (IdentifierExpressionNode) name
						.copy();
				newNode.getIdentifier().setEntity(entity);
				privateIDs.addSequenceChild(newNode);
			}
		} else {
			for (ASTNode child : node.children()) {
				if (child instanceof OperatorNode) {
					getInitializerName((OperatorNode) child, alreadyDeclVars,
							privateIDs);
				}
			}
		}
	}

	private void getInitializerName(DeclarationListNode node,
			ArrayList<String> loopVariables) {

	}

	private boolean getImplicitShared(
			SequenceNode<IdentifierExpressionNode> sharedIDs, ASTNode node,
			ArrayList<String> declaredNodes, ArrayList<String> currentShared,
			ArrayList<String> loopVars, boolean removed) {
		for (ASTNode child : node.children()) {
			if (child != null && !(child.parent() instanceof FunctionCallNode)) {
				if (child instanceof IdentifierExpressionNode) {
					String temp = ((IdentifierExpressionNode) child)
							.getIdentifier().name();
					boolean reductionNode = false;
					if (temp.contains("_reduction")) {
						temp = temp.replace("_reduction", "");
						reductionNode = true;
					}

					ASTNode parent = child;
					boolean functionParam = false;
					boolean loopVar = false;
					while (!(parent instanceof FunctionDefinitionNode)) {
						parent = parent.parent();
					}

					parent = child;
					while (!(parent instanceof FunctionDefinitionNode)) {
						if (parent instanceof OmpForNode) {
							OmpForNode forLoop = (OmpForNode) parent;
							ASTNode forNode = forLoop.statementNode();
							for (ASTNode forChild : forNode.children()) {
								if (forChild != null && forChild.equals(node)) {
									loopVar = true;
									loopVars.add(temp);
								}
							}
						}

						parent = parent.parent();
					}

					if ((!(declaredNodes.contains(temp) || currentShared
							.contains(temp)))
							&& !loopVars.contains(temp)
							&& !temp.equals(TID) && !functionParam && !loopVar) {
						Entity entity = ((IdentifierExpressionNode) child)
								.getIdentifier().getEntity();
						IdentifierExpressionNode newNode = (IdentifierExpressionNode) child
								.copy();
						if (reductionNode) {
							newNode.getIdentifier().setName(temp);
						}

						newNode.getIdentifier().setEntity(entity);
						sharedIDs.addSequenceChild(newNode);
						currentShared.add(temp);
					}
				}

				if (child instanceof VariableDeclarationNode) {
					ASTNode parent = child;
					boolean functionParam = false;
					while (!(parent instanceof FunctionDefinitionNode)) {
						if (parent instanceof FunctionTypeNode) {
							functionParam = true;
						}
						parent = parent.parent();
					}
					if (!functionParam) {
						String temp = ((DeclarationNode) child).getIdentifier()
								.name();
						declaredNodes.add(temp);
						if (currentShared.contains(temp)) {
							currentShared.remove(temp);
						}
						for (IdentifierExpressionNode id : sharedIDs) {
							if (id != null) {
								if (id.getIdentifier().name().equals(temp)) {
									int index = id.childIndex();
									sharedIDs.removeChild(index);
									removed = true;
								}
							}

						}
					}
				}

				removed = getImplicitShared(sharedIDs, child, declaredNodes,
						currentShared, loopVars, removed) || removed;
			}
		}
		return removed;
	}

	private void checkArrayIndices(OperatorNode op,
			SequenceNode<IdentifierExpressionNode> privateIDs,
			SequenceNode<IdentifierExpressionNode> sharedIDs,
			SequenceNode<IdentifierExpressionNode> reductionIDs,
			SequenceNode<IdentifierExpressionNode> firstPrivateIDs,
			SequenceNode<IdentifierExpressionNode> threadPrivateIDs)
			throws SyntaxException, NoSuchElementException {
		replaceOMPPragmas(op.child(1), privateIDs, sharedIDs, reductionIDs,
				firstPrivateIDs, threadPrivateIDs);
		ASTNode lhs = op.child(0);
		while (lhs instanceof OperatorNode) {
			replaceOMPPragmas(lhs.child(1), privateIDs, sharedIDs,
					reductionIDs, firstPrivateIDs, threadPrivateIDs);
			lhs = lhs.child(0);
		}
	}

	/**
	 * 
	 * Adds appropriate headers to the program
	 * 
	 * 
	 * @param root
	 *            The root node of the AST of the original OpenMP program.
	 * @return The function definition node of OpenMP, the list of AST nodes
	 *         that are parsed from header files and will be moved up to the
	 *         higher scope (i.e., the file scope of the final AST), and the
	 *         list of variable declaration nodes.
	 * @throws SyntaxException
	 */
	private Triple<List<BlockItemNode>, List<BlockItemNode>, List<VariableDeclarationNode>> program(
			SequenceNode<BlockItemNode> root) throws SyntaxException {
		List<BlockItemNode> includedNodes = new ArrayList<>();
		List<VariableDeclarationNode> vars = new ArrayList<>();
		List<BlockItemNode> items;
		int number;
		items = new LinkedList<>();
		number = root.numChildren();

		final String place = "numThreadsDeclaration";
		TypeNode nthreadsType = nodeFactory.newBasicTypeNode(
				newSource(place, CivlcTokenConstant.INT), BasicTypeKind.INT);
		IdentifierNode identifierNode = nodeFactory.newIdentifierNode(
				newSource(place, CivlcTokenConstant.IDENTIFIER), OMPPRE
						+ "num_threads");

		items.add(nodeFactory.newVariableDeclarationNode(
				newSource(place, CivlcTokenConstant.DECLARATION),
				identifierNode, nthreadsType, this.identifierExpression(
						newSource(place, CivlcTokenConstant.IDENTIFIER),
						THREADMAX)));

		for (ASTNode node : structsDefsToAdd) {
			items.add((BlockItemNode) node);
		}

		for (ASTNode node : structsToAdd) {
			items.add((BlockItemNode) node);
		}

		for (int i = 0; i < number; i++) {
			BlockItemNode child = root.getSequenceChild(i);
			String sourceFile;

			if (child == null)
				continue;
			sourceFile = child.getSource().getFirstToken().getSourceFile()
					.getName();
			root.removeChild(i);
			if (sourceFile.equals("omp.cvl")) {
				includedNodes.add(child);
			} else if (sourceFile.endsWith(".cvh")
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
				items.add(child);
			}
		}

		return new Triple<>(items, includedNodes, vars);
	}

	/**
	 * Extracting bounds and step for ranges from a Canonical ForLoopNode
	 * 
	 * @param forloopNode
	 *            The AST Node represents a canonical for loop. (Pre-condition:
	 *            The for loop should be more strictly a canonical for loop.)
	 * @return A triple of lower bound , higher bound and step
	 * @throws SyntaxException
	 */
	private Triple<ASTNode, ASTNode, ASTNode> canonicalForLoopBounds(
			ForLoopNode forloopNode) throws SyntaxException {
		IdentifierNode loopVar;
		ForLoopInitializerNode initializer;
		IdentifierExpressionNode identExpr;
		ExpressionNode conditioner;
		ExpressionNode incrementor;
		OperatorNode incNode;
		ASTNode lo = null;
		ASTNode hi = null;
		ASTNode step = null;
		ASTNode one = nodeFactory.newIntegerConstantNode((Source) null, "1");
		ASTNode zero = nodeFactory.newIntegerConstantNode((Source) null, "0");
		ASTNode newHi;
		Operator incOp, stepSign;
		boolean isNegativeIncrement = false;

		initializer = forloopNode.getInitializer();
		conditioner = forloopNode.getCondition();
		incrementor = forloopNode.getIncrementer();
		// Initializer can either be a OperatorNode or a DeclarationListNode:
		// for(i = 0;...) or for(int i = 0; ...)
		if (initializer instanceof OperatorNode) {
			// OperatorNode means it's an assignment statement e.g. i = 0;
			// So the initial value is child(1).
			lo = initializer.child(1);
			// Obtain the identifierNode of the loop variable which will be used
			// to distinguish between a loop variable and a regular variable in
			// termination and incrementor.
			loopVar = ((IdentifierExpressionNode) initializer.child(0))
					.getIdentifier();
		} else if (initializer instanceof DeclarationListNode) {
			VariableDeclarationNode varDecNode = (VariableDeclarationNode) initializer
					.child(0);

			// The initializer has a similar form as "int i = 0"
			lo = varDecNode.getInitializer();
			loopVar = (IdentifierNode) varDecNode.getIdentifier();
		} else {
			throw new CIVLSyntaxException("OpenMP for loop initializer");
		}
		// The bound value in conditioner can either be in the left hand side or
		// right hand side of a comparison operator(GT, LT, GTE, LTE).
		if (conditioner instanceof OperatorNode) {
			if (conditioner.child(0) instanceof IdentifierExpressionNode) {
				identExpr = (IdentifierExpressionNode) conditioner.child(0);

				if (identExpr.getIdentifier().getEntity()
						.equals(loopVar.getEntity()))
					hi = conditioner.child(1);
			}
			if (hi == null
					&& conditioner.child(1) instanceof IdentifierExpressionNode) {
				identExpr = (IdentifierExpressionNode) conditioner.child(1);

				if (identExpr.getIdentifier().getEntity()
						.equals(loopVar.getEntity()))
					hi = conditioner.child(0);
			}
		}
		if (hi == null)
			throw new CIVLSyntaxException("OpenMP for loop conditioner");
		// Incrementor has three basic forms. e.g. i++ (--), i+=1, i = i + 1,
		// what in common is all of them are operatorNodes.
		assert incrementor instanceof OperatorNode;
		incNode = (OperatorNode) incrementor;
		incOp = incNode.getOperator();
		if (incNode.getOperator() == Operator.ASSIGN) {
			assert incrementor.child(1) instanceof OperatorNode : "OpenMP for loop incrementor";
			incNode = (OperatorNode) incrementor.child(1);
			incOp = incNode.getOperator();
			if (incNode.child(0) instanceof IdentifierExpressionNode) {
				if (((IdentifierExpressionNode) incNode.child(0))
						.getIdentifier().getEntity()
						.equals(loopVar.getEntity()))
					step = incNode.child(1);
			} else
				step = incNode.child(0);

		} else {
			if (incNode.numChildren() == 1)
				step = nodeFactory.newIntegerConstantNode(
						incrementor.getSource(), "1");
			else if (incNode.numChildren() == 2)
				step = incNode.child(1);
		}
		// If the incrementor increase the loop variable or decrease it.
		if (incOp == Operator.POSTDECREMENT || incOp == Operator.MINUSEQ
				|| incOp == Operator.MINUS) {
			step = nodeFactory.newOperatorNode(incrementor.getSource(),
					Operator.MINUS, Arrays.asList((ExpressionNode) zero.copy(),
							(ExpressionNode) step.copy()));
			isNegativeIncrement = true;
		}
		newHi = nodeFactory.newOperatorNode(
				newSource("rangeHi", CivlcTokenConstant.EXPR),
				Operator.PLUS,
				Arrays.asList((ExpressionNode) lo.copy(),
						(ExpressionNode) hi.copy()));
		// If the termination bound is open, change the bound by one. (Since
		// canonical only accept integer loop variable, it's safe)
		if (((OperatorNode) conditioner).getOperator() == Operator.LT
				|| ((OperatorNode) conditioner).getOperator() == Operator.GT) {
			if (isNegativeIncrement) {
				stepSign = Operator.PLUS;
			} else
				stepSign = Operator.MINUS;
			newHi = nodeFactory.newOperatorNode(
					newSource("rangeHi", CivlcTokenConstant.EXPR), stepSign,
					Arrays.asList((ExpressionNode) hi.copy(),
							(ExpressionNode) one.copy()));
		} else
			newHi = hi.copy();
		// Since $range will always put the larger value at the right hand side
		// of the "..", so if the operator of the incrementor is -- -= or -, we
		// have to switch the high bound and the lower bound.
		if (isNegativeIncrement) {
			ASTNode temp = newHi;

			newHi = lo;
			lo = temp;
		}
		return new Triple<>(lo, newHi, step);
	}

	private void fix_duplicated_barrier_flush(ASTNode root, boolean isMain) {
		this.reduceDuplicateNode(root, new NodePredicate() {
			@Override
			public boolean holds(ASTNode node) {
				return isFunctionCallStatementNodeOf(node,
						"$omp_barrier_and_flush");

			}
		});

	}

	private boolean isFunctionCallStatementNodeOf(ASTNode node, String function) {
		if (node instanceof ExpressionStatementNode) {
			ExpressionNode expression = ((ExpressionStatementNode) node)
					.getExpression();

			if (expression instanceof FunctionCallNode) {
				ExpressionNode functionNode = ((FunctionCallNode) expression)
						.getFunction();

				if (functionNode instanceof IdentifierExpressionNode) {
					return ((IdentifierExpressionNode) functionNode)
							.getIdentifier().name().equals(function);
				}
			}
		}
		return false;
	}

}
