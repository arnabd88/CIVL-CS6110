package edu.udel.cis.vsl.civl.model.common;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashSet;

import edu.udel.cis.vsl.abc.ast.entity.IF.Function;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode.NodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.FunctionTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode.TypeNodeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.FunctionType;
import edu.udel.cis.vsl.civl.err.CIVLSyntaxException;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Fragment;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.MPIModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression.BINARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression.UNARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.util.Pair;

/**
 * Translates MPI specific functions. For example, MPI_Send(), MPI_Recv(), etc.
 * Moreover, generates the function for the "root" process.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class MPIFunctionTranslator extends FunctionTranslator {

	/* ************************** Instance Fields ************************** */

	/**
	 * The unique MPI model factory used by the system.
	 */
	private MPIModelFactory mpiFactory;

	/**
	 * The unique MPI model builder worker used by the system.
	 */
	private MPIModelBuilderWorker mpiModelBuilder;

	/* **************************** Constructors *************************** */

	/**
	 * Create a new instance of MPI function translator.
	 * 
	 * @param mpiModelBuilder
	 *            The MPI model builder worker to be used..
	 * @param mpiFactory
	 *            The MPI model factory to be used.
	 * @param function
	 *            The CIVL function that this translator targets.
	 */
	MPIFunctionTranslator(MPIModelBuilderWorker mpiModelBuilder,
			MPIModelFactory mpiFactory, CIVLFunction function) {
		super(mpiModelBuilder, mpiFactory, function);
		this.mpiFactory = mpiFactory;
		this.mpiModelBuilder = mpiModelBuilder;
	}

	/**
	 * Create a new instance of MPI function translator.
	 * 
	 * @param mpiModelBuilder
	 *            The MPI model builder worker to be used..
	 * @param mpiFactory
	 *            The MPI model factory to be used.
	 * @param function
	 *            The CIVL function that this translator targets.
	 * @param functionBody
	 *            The AST node of the function body.
	 */
	MPIFunctionTranslator(MPIModelBuilderWorker mpiModelBuilder,
			MPIModelFactory mpiFactory, CIVLFunction function,
			StatementNode functionBody) {
		super(mpiModelBuilder, mpiFactory, function);
		this.mpiFactory = mpiFactory;
		this.mpiModelBuilder = mpiModelBuilder;
		this.functionBodyNode = functionBody;
	}

	/* *************************** Public Methods ************************** */
	/**
	 * Iterates on the children of the root node of the program to find the main
	 * function definition node, and create the (incomplete) CIVL function
	 * accordingly. An extra parameter $RANK is added into the main function.
	 * 
	 * @param systemScope
	 *            The root scope of the system.
	 * @param rootNode
	 *            The root node of the AST tree of the program.
	 * @return The (incomplete) CIVL function representing the main function for
	 *         MPI processes.
	 */
	public CIVLFunction processMainFunction(Scope systemScope, ASTNode rootNode) {
		FunctionDefinitionNode processMainNode = null;
		CIVLFunction mainFunction;

		for (int i = 0; i < rootNode.numChildren(); i++) {
			ASTNode node = rootNode.child(i);

			if (node.nodeKind() == NodeKind.FUNCTION_DEFINITION) {
				FunctionDefinitionNode functionDefinitionNode = (FunctionDefinitionNode) node;

				if (functionDefinitionNode.getName().equals("main")) {
					mpiModelBuilder.mainFunctionNode = functionDefinitionNode;
					processMainNode = functionDefinitionNode;
					break;
				}
			}
		}
		if (processMainNode == null) {
			throw new CIVLSyntaxException("program must have a main function,",
					mpiFactory.sourceOf(rootNode));
		} else {
			Function entity = processMainNode.getEntity();
			CIVLSource nodeSource = mpiFactory.sourceOf(processMainNode);
			CIVLSource identifierSource = mpiFactory.sourceOf(processMainNode
					.getIdentifier());
			Identifier functionIdentifier = mpiFactory.identifier(
					identifierSource, "main");
			ArrayList<Variable> parameters = new ArrayList<Variable>();
			// type should come from entity, not this type node.
			// if it has a definition node, should probably use that one.
			FunctionType functionType = entity.getType();
			FunctionTypeNode functionTypeNode = (FunctionTypeNode) processMainNode
					.getTypeNode();
			CIVLType returnType = translateABCType(
					mpiFactory.sourceOf(functionTypeNode.getReturnType()),
					systemScope, functionType.getReturnType());
			SequenceNode<VariableDeclarationNode> abcParameters = functionTypeNode
					.getParameters();
			int numParameters = abcParameters.numChildren();

			for (int i = 0; i < numParameters; i++) {
				VariableDeclarationNode decl = abcParameters
						.getSequenceChild(i);
				CIVLType type;
				CIVLSource source;
				Identifier variableName;

				// Don't process void types. Should only happen in the prototype
				// of a function with no parameters.
				if (decl.getTypeNode().kind() == TypeNodeKind.VOID)
					continue;
				type = translateABCType(mpiFactory.sourceOf(decl), systemScope,
						functionType.getParameterType(i));
				source = mpiFactory.sourceOf(decl.getIdentifier());
				variableName = mpiFactory.identifier(source, decl.getName());
				parameters.add(mpiFactory.variable(source, type, variableName,
						parameters.size()));
			}
			if (entity.getDefinition() == null) {
				throw new CIVLSyntaxException(
						"The definition of the main function cannot be found.",
						identifierSource);
			}
			mpiFactory.createRankVariable(parameters.size());
			parameters.add(mpiFactory.rankVariable().variable());
			mainFunction = mpiFactory.function(nodeSource, functionIdentifier,
					parameters, returnType, systemScope, null);
		}
		return mainFunction;
	}

	/**
	 * The root function is the system function, which is responsible for:
	 * <ul>
	 * <li>
	 * initialize the synchronizing variable $START=0;</li>
	 * <li>
	 * spawn MPI processes;</li>
	 * <li>
	 * initialize MPI_Comm_Worls;</li>
	 * <li>
	 * update the synchronizing variable $START=1;</li>
	 * <li>
	 * wait for MPI processes' termination.</li>
	 * </ul>
	 * 
	 * @param systemScope
	 *            The root scope of the system.
	 * @param rootNode
	 *            The root node of the AST tree of the program.
	 * @param processMainScope
	 *            The outer scope of the main function of MPI processes.
	 */
	public Fragment translateRootFunction(Scope systemScope, ASTNode rootNode,
			Scope processMainScope) {
		Pair<Fragment, Fragment> init = translateRootNodes(processMainScope,
				rootNode);

		translateRootFunctionBody(systemScope, init.left);
		return init.right;
	}

	/**
	 * Translate the main function. Making the first statement of the function
	 * body guarded by $START==1.
	 * 
	 * @param initialization
	 *            The fragment of initialization statements before the main
	 *            function.
	 */
	public void translateProcessMainFunction(Fragment initialization) {
		Fragment body;
		Expression startGuard;

		body = this.translateFunctionBody();
		body = initialization.combineWith(body);
		startGuard = mpiFactory.binaryExpression(null, BINARY_OPERATOR.EQUAL,
				mpiFactory.startVariable(), mpiFactory
						.integerLiteralExpression(null, BigInteger.valueOf(1)));
		body.addGuardToStartLocation(startGuard, mpiFactory);
		functionInfo.completeFunction(body);
	}

	/* *************************** Private Methods ************************* */

	/**
	 * Compose a loop fragment.
	 * 
	 * @param initFragment
	 *            The initialization of the loop.
	 * @param loopEntrance
	 *            The entrance of the loop.
	 * @param loopBody
	 *            The loop body of the loop.
	 * @param incrementer
	 *            The incrementer of the loop.
	 * @param loopExit
	 *            The exit statement of the loop.
	 * @return The result-in loop fragment.
	 */
	private Fragment composeLoop(Fragment initFragment, Fragment loopEntrance,
			Fragment loopBody, Fragment incrementer, Statement loopExit) {
		Fragment result;

		// incrementer comes after the loop body
		if (incrementer != null)
			loopBody = loopBody.combineWith(incrementer);
		// loop entrance comes before the loop body, P.S. loopExit is "combined"
		// implicitly because its start location is the same as loopEntrance
		loopBody = loopBody.combineWith(loopEntrance);
		// initially loop entrance comes before the loopBody. Now we'll have
		// loopBody -> loopEntrance -> loopBody and the loop is formed.
		result = loopEntrance.combineWith(loopBody);
		result.setLastStatement(loopExit);
		return result;
	}

	/**
	 * Create the fragment for spawning MPI processes.
	 * 
	 * @param scope
	 *            The scope of the start location of the result fragment.
	 * @param numberOfProcs
	 *            The number of processes that are to be spawned.
	 * @return The fragment of statements for spawning MPI processes.
	 */
	private Fragment spawnMpiProcesses(Scope scope, Expression numberOfProcs) {
		Scope newScope = mpiFactory.scope(scope, new LinkedHashSet<Variable>(),
				functionInfo().function());
		Fragment initFragment, result;
		Location location = mpiFactory.location(newScope);
		Variable iVariable = mpiFactory.variable(mpiFactory.integerType(),
				mpiFactory.identifier("i"), newScope.numVariables());
		VariableExpression iVariableExpression = mpiFactory
				.variableExpression(iVariable);
		Expression condition = mpiFactory.binaryExpression(
				mpiFactory.systemSource(), BINARY_OPERATOR.LESS_THAN,
				iVariableExpression, numberOfProcs);
		Location loopEntranceLocation = mpiFactory.location(newScope), loopBodyLocation = mpiFactory
				.location(newScope);
		Fragment loopEntrance = new CommonFragment(loopEntranceLocation,
				mpiFactory.loopBranchStatement(mpiFactory.systemSource(),
						loopEntranceLocation, condition, true));
		Fragment loopBody, incrementer;
		Statement loopExit = mpiFactory.loopBranchStatement(condition
				.getSource(), loopEntranceLocation, mpiFactory.unaryExpression(
				condition.getSource(), UNARY_OPERATOR.NOT, condition), false);
		ArrayList<Expression> arguments = new ArrayList<>();
		CallOrSpawnStatement mpiSpawn;

		initFragment = new CommonFragment(mpiFactory.assignStatement(location,
				iVariableExpression,
				mpiFactory.integerLiteralExpression(BigInteger.valueOf(0)),
				true));
		arguments.add(iVariableExpression);// the argument is the value of rank.
		mpiSpawn = mpiFactory.callOrSpawnStatement(loopBodyLocation, false,
				mpiModelBuilder.processMainFunction(), arguments);
		mpiSpawn.setLhs(mpiFactory.subscriptExpression(null,
				mpiFactory.procsVariable(), iVariableExpression));
		newScope.addVariable(iVariable);
		loopBody = new CommonFragment(mpiSpawn);
		incrementer = new CommonFragment(mpiFactory.assignStatement(mpiFactory
				.location(newScope), iVariableExpression, mpiFactory
				.binaryExpression(mpiFactory.systemSource(),
						BINARY_OPERATOR.PLUS, iVariableExpression,
						mpiFactory.integerLiteralExpression(BigInteger
								.valueOf(1))), false));
		result = composeLoop(initFragment, loopEntrance, loopBody, incrementer,
				loopExit);
		result = initFragment.combineWith(result);
		return result;
	}

	/**
	 * Translate and complete the root function body.
	 * 
	 * @param systemScope
	 *            The root scope of the system.
	 */
	private void translateRootFunctionBody(Scope systemScope, Fragment init) {
		Fragment result;
		Fragment initStartFragment, initProcsFragment;
		Fragment spawnPhase;
		Fragment waitPhase;
		Location returnLocation;
		Fragment returnFragment;
		Fragment createCommFragment, assignStartFragment;
		Location atomicStart = mpiFactory.location(systemScope);
		Variable mpiCommWorld = systemScope.variable(mpiFactory
				.identifier(MPIModelFactory.MPI_COMM_WORLD));
		ArrayList<Expression> createCommArguments = new ArrayList<>();
		ArrayList<Variable> commCreateParameters = new ArrayList<>();
		CIVLFunction createCommFunction;

		mpiFactory.createStartVariable(systemScope, systemScope.numVariables());
		mpiFactory.createProcsVariable(systemScope, systemScope.numVariables(),
				mpiFactory.numberOfProcs());
		initStartFragment = new CommonFragment(mpiFactory.assignStatement(
				mpiFactory.location(systemScope), mpiFactory.startVariable(),
				mpiFactory.integerLiteralExpression(BigInteger.valueOf(0)),
				true));
		initProcsFragment = new CommonFragment(mpiFactory.assignStatement(
				mpiFactory.location(systemScope), mpiFactory.procsVariable(),
				mpiFactory.initialValueExpression(mpiFactory.systemSource(),
						mpiFactory.procsVariable().variable()), true));
		spawnPhase = spawnMpiProcesses(systemScope, mpiFactory.numberOfProcs());
		commCreateParameters.add(mpiFactory.variable(mpiFactory.numberOfProcs()
				.getExpressionType(), mpiFactory.identifier("nprocs"),
				commCreateParameters.size()));
		commCreateParameters.add(mpiFactory.variable(mpiFactory.procsVariable()
				.getExpressionType(), mpiFactory.identifier("procs"),
				commCreateParameters.size()));
		createCommFunction = mpiFactory
				.systemFunction(mpiFactory.systemSource(),
						mpiFactory.identifier(MPIModelFactory.COMMM_CREATE),
						commCreateParameters, mpiFactory.voidType(),
						systemScope, "mpi");
		createCommArguments.add(mpiFactory.numberOfProcs());
		createCommArguments.add(mpiFactory.procsVariable());
		createCommFragment = new CommonFragment(
				mpiFactory.callOrSpawnStatement(mpiFactory
						.location(systemScope), true, mpiFactory
						.variableExpression(mpiCommWorld.getSource(),
								mpiCommWorld), createCommFunction,
						createCommArguments));
		assignStartFragment = new CommonFragment(mpiFactory.assignStatement(
				mpiFactory.location(systemScope), mpiFactory.startVariable(),
				mpiFactory.integerLiteralExpression(BigInteger.valueOf(1)),
				false));
		waitPhase = waitMpiProcesses(systemScope, mpiFactory.numberOfProcs());
		result = init.combineWith(initStartFragment);
		result = result.combineWith(initProcsFragment);
		result = result.combineWith(spawnPhase);
		result = result.combineWith(createCommFragment);
		result = result.combineWith(assignStartFragment);
		result = result.combineWith(waitPhase);
		result = mpiFactory.atomicFragment(false, result, atomicStart,
				mpiFactory.location(systemScope));
		returnLocation = mpiFactory.location(function().outerScope());
		returnFragment = mpiFactory.returnFragment(mpiFactory.systemSource(),
				returnLocation, null, functionInfo().function());
		result = result.combineWith(returnFragment);
		functionInfo().completeFunction(result);
	}

	/**
	 * Iterates over all children, which are variable and function declaration
	 * nodes and so on, of the root node of the AST tree, except for the main
	 * function definition node.<br>
	 * Nodes translated here included:
	 * 
	 * @param mainScope
	 * @param rootNode
	 * @return
	 */
	private Pair<Fragment, Fragment> translateRootNodes(Scope mainScope,
			ASTNode rootNode) {
		Fragment root = new CommonFragment(), main = new CommonFragment();
		Scope systemScope = mainScope.parent();

		mpiFactory.addConditionalExpressionQueue();
		for (int i = 0; i < rootNode.numChildren(); i++) {
			ASTNode node = rootNode.child(i);
			Scope scope = mainScope;
			Fragment fragment;
			boolean isRoot = false;

			if (node.getSource().getLastToken().getSourceFile().getName()
					.equalsIgnoreCase("mpi.h")) {
				isRoot = true;
				scope = systemScope;
			}
			fragment = translateASTNode(node, scope, null);
			if (isRoot)
				root = root.combineWith(fragment);
			else
				main = main.combineWith(fragment);
		}
		mpiFactory.popConditionaExpressionStack();
		return new Pair<>(root, main);
	}

	/**
	 * Create the fragment for waiting for MPI processes.
	 * 
	 * @param scope
	 *            The scope of the start location of the result fragment.
	 * @param numberOfProcs
	 *            The number of processes that are to be waited.
	 * @return The fragment of statements for waiting for MPI processes.
	 */
	private Fragment waitMpiProcesses(Scope scope, Expression numberOfProcs) {
		Scope newScope = mpiFactory.scope(scope, new LinkedHashSet<Variable>(),
				functionInfo().function());
		Fragment initFragment, result;
		Location location = mpiFactory.location(newScope);
		Variable iVariable = mpiFactory.variable(mpiFactory.integerType(),
				mpiFactory.identifier("i"), newScope.numVariables());
		VariableExpression iVariableExpression = mpiFactory
				.variableExpression(iVariable);
		Expression condition = mpiFactory.binaryExpression(
				mpiFactory.systemSource(), BINARY_OPERATOR.LESS_THAN,
				iVariableExpression, numberOfProcs);
		Location loopEntranceLocation = mpiFactory.location(newScope), loopBodyLocation = mpiFactory
				.location(newScope);
		Fragment loopEntrance = new CommonFragment(loopEntranceLocation,
				mpiFactory.loopBranchStatement(mpiFactory.systemSource(),
						loopEntranceLocation, condition, true));
		Fragment loopBody, incrementer;
		Statement loopExit = mpiFactory.loopBranchStatement(condition
				.getSource(), loopEntranceLocation, mpiFactory.unaryExpression(
				condition.getSource(), UNARY_OPERATOR.NOT, condition), false);

		newScope.addVariable(iVariable);
		initFragment = new CommonFragment(mpiFactory.assignStatement(location,
				iVariableExpression,
				mpiFactory.integerLiteralExpression(BigInteger.valueOf(0)),
				true));
		loopBody = mpiFactory.joinFragment(mpiFactory.systemSource(),
				loopBodyLocation, mpiFactory.subscriptExpression(null,
						mpiFactory.procsVariable(), iVariableExpression));
		incrementer = new CommonFragment(mpiFactory.assignStatement(mpiFactory
				.location(newScope), iVariableExpression, mpiFactory
				.binaryExpression(mpiFactory.systemSource(),
						BINARY_OPERATOR.PLUS, iVariableExpression,
						mpiFactory.integerLiteralExpression(BigInteger
								.valueOf(1))), false));
		result = composeLoop(initFragment, loopEntrance, loopBody, incrementer,
				loopExit);
		result = initFragment.combineWith(result);
		return result;
	}

	/* ****************** Methods from Function Translator ***************** */

	/**
	 * {@inheritDoc} For MPI function calls, they are translated to the
	 * corresponding MPI statement, like MPISendStatement, MPIRecvStatement,
	 * etc.
	 */
	@Override
	protected Statement translateFunctionCall(Scope scope, LHSExpression lhs,
			FunctionCallNode functionCallNode, boolean isCall) {
		CIVLSource source = modelFactory().sourceOfBeginning(functionCallNode);
		String functionName = ((IdentifierExpressionNode) functionCallNode
				.getFunction()).getIdentifier().name();
		ArrayList<Expression> arguments = new ArrayList<Expression>();
		Location location;

		for (int i = 0; i < functionCallNode.getNumberOfArguments(); i++) {
			Expression actual = translateExpressionNode(
					functionCallNode.getArgument(i), scope, true);

			actual = arrayToPointer(actual);
			arguments.add(actual);
		}
		location = mpiFactory.location(mpiFactory.sourceOf(functionCallNode),
				scope);
		switch (functionName) {
		// translate mpi function calls to the corresponding MPI
		// Statement.
		case MPIModelFactory.MPI_SEND:
			return mpiFactory
					.mpiSendStatement(source, location, lhs, arguments);
		case MPIModelFactory.MPI_RECV:
			return mpiFactory
					.mpiRecvStatement(source, location, lhs, arguments);
		case MPIModelFactory.MPI_ISEND:
			return mpiFactory.mpiIsendStatement(source, location, lhs,
					arguments);
		case MPIModelFactory.MPI_IRECV:
			return mpiFactory.mpiIrecvStatement(source, location, lhs,
					arguments);
		case MPIModelFactory.MPI_BARRIER:
			return mpiFactory.mpiBarrierStatement(source, location, lhs,
					arguments);
		case MPIModelFactory.MPI_WAIT:
			return mpiFactory
					.mpiWaitStatement(source, location, lhs, arguments);
		default:
			return callOrSpawnStatement(location, functionCallNode, lhs,
					arguments, isCall);
		}
	}

}
