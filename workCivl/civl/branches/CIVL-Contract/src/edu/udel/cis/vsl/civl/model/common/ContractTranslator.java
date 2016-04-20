package edu.udel.cis.vsl.civl.model.common;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.abc.ast.entity.IF.Function;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.AssignsOrReadsNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.AssumesNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.BehaviorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.CallEventNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.CompositeEventNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.ContractNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.DependsEventNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.DependsEventNode.DependsEventNodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.DependsNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.EnsuresNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.GuardsNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPICollectiveBlockNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPIContractConstantNode.MPIConstantKind;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPIContractExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPIContractExpressionNode.MPIContractExpressionKind;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MemoryEventNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.RequiresNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode.ExpressionKind;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ResultNode;
import edu.udel.cis.vsl.abc.ast.node.common.acsl.CommonMPIConstantNode;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLSyntaxException;
import edu.udel.cis.vsl.civl.model.IF.CIVLTypeFactory;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.contract.CallEvent;
import edu.udel.cis.vsl.civl.model.IF.contract.CompositeEvent.CompositeEventOperator;
import edu.udel.cis.vsl.civl.model.IF.contract.ContractFactory;
import edu.udel.cis.vsl.civl.model.IF.contract.DependsEvent;
import edu.udel.cis.vsl.civl.model.IF.contract.DependsEvent.DependsEventKind;
import edu.udel.cis.vsl.civl.model.IF.contract.FunctionBehavior;
import edu.udel.cis.vsl.civl.model.IF.contract.FunctionContract;
import edu.udel.cis.vsl.civl.model.IF.contract.FunctionContract.ContractKind;
import edu.udel.cis.vsl.civl.model.IF.contract.MPICollectiveBehavior;
import edu.udel.cis.vsl.civl.model.IF.contract.MPICollectiveBehavior.MPICommunicationPattern;
import edu.udel.cis.vsl.civl.model.IF.contract.NamedFunctionBehavior;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression.BINARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.MPIContractExpression.MPI_CONTRACT_EXPRESSION_KIND;
import edu.udel.cis.vsl.civl.model.IF.expression.Nothing;
import edu.udel.cis.vsl.civl.model.IF.expression.PointerSetExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression.UNARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPointerType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.model.common.contract.CommonContractFactory;
import edu.udel.cis.vsl.civl.util.IF.Pair;

public class ContractTranslator extends FunctionTranslator {
	/**
	 * The string type name of the Result Expression:<br>
	 * An special expression used to represent the result of a function in
	 * function contracts.
	 */
	// TODO: move this to model configuration
	public static final String contractResultName = "\\result";
	public static final String contractMPICommRankName = "\\mpi_comm_rank";
	public static final String contractMPICommSizeName = "\\mpi_comm_size";

	private CIVLFunction function;

	private ModelFactory modelFactory;

	private ModelBuilderWorker modelBuilder;

	private ContractFactory contractFactory = new CommonContractFactory();

	private ContractKind currentContractKind;

	private Expression currentMPICommunicator;

	/******************** Constructor ********************/
	ContractTranslator(ModelBuilderWorker modelBuilder,
			ModelFactory modelFactory, CIVLTypeFactory typeFactory,
			CIVLFunction function) {
		super(modelBuilder, modelFactory, function);
		this.modelFactory = modelFactory;
		this.modelBuilder = modelBuilder;
		this.function = function;
	}

	public void translateFunctionContract(SequenceNode<ContractNode> contract) {
		FunctionContract result = contractFactory
				.newFunctionContract(modelFactory.sourceOf(contract));

		for (ContractNode clause : contract) {
			this.translateContractNode(clause, result);
		}
		this.function.setFunctionContract(result);
	}

	private void translateContractNode(ContractNode contractNode,
			FunctionContract functionContract) {
		this.translateContractNodeWork(contractNode, functionContract, null,
				null);
	}

	/**
	 * Translates a {@link ContractNode} to a component of a
	 * {@link FunctionContract}.
	 * 
	 * The function takes at most three main components:
	 * {@link FunctionContract}, {@link MPICollectiveBehavior} and
	 * {@link NamedFunctionBehavior}. According to the syntax:
	 * <p>
	 * <ol>
	 * <li>None of them can be nested.</li>
	 * <li>{@link NamedFunctionBehavior} can appear in {@link FunctionContract}
	 * or {@link MPICollectiveBehavior}</li>
	 * <li>{@link MPICollectiveBehavior} can only appear in
	 * {@link FunctionContract}</li>
	 * <li>{@link FunctionContract} denotes the whole group of function
	 * contracts for a function. For each function, it can has at most one
	 * {@link FunctionContract}.</li>
	 * </ol>
	 * </p>
	 * Thus, the specifications for different kind of contracts is as follows:
	 * <p>
	 * <ol>
	 * <li>
	 * A {@link NamedFunctionBehavior} will be added as a component of a
	 * {@link MPICollectiveBehavior} if it is non-null, else as of a
	 * {@link FunctionContract}.</li>
	 * <li>{@link ASSUMES} can only be added as a component of a
	 * {@link NamedFunctionBehavior}</li>
	 * <li>Other contract clauses will be added as a component of one of the
	 * three main blocks with such a precedence:
	 * <code>{@link NamedFunctionBehavior} higher than {@link MPICollectiveBehavior} high than {@link FunctionContract}<code>
	 * </li>
	 * </ol>
	 * </p>
	 * 
	 * @param contractNode
	 * @return
	 */
	private void translateContractNodeWork(ContractNode contractNode,
			FunctionContract functionContract,
			MPICollectiveBehavior collectiveBehavior,
			NamedFunctionBehavior behavior) {
		CIVLSource source = modelFactory.sourceOf(contractNode);
		Scope scope = function.outerScope();
		FunctionBehavior targetBehavior = behavior != null ? behavior
				: collectiveBehavior != null ? collectiveBehavior
						: functionContract.defaultBehavior();

		switch (contractNode.contractKind()) {
		case ASSIGNS_READS: {
			AssignsOrReadsNode assignsOrReads = (AssignsOrReadsNode) contractNode;
			boolean isAssigns = assignsOrReads.isAssigns();
			SequenceNode<ExpressionNode> muNodes = assignsOrReads
					.getMemoryList();

			for (ExpressionNode muNode : muNodes) {
				Expression mu = this.translateExpressionNode(muNode, scope,
						true);

				if (mu instanceof Nothing) {
					if (isAssigns) {
						if (targetBehavior.numAssignsMemoryUnits() == 0)
							targetBehavior.setAssingsNothing();
						else
							throw new CIVLSyntaxException(
									"assigns \\nothing conflicts with previous assigns clause",
									source);
					} else {
						if (targetBehavior.numAssignsMemoryUnits() == 0)
							targetBehavior.setReadsNothing();
						else
							throw new CIVLSyntaxException(
									"reads \\nothing conflicts with previous reads clause",
									source);
					}
				} else {
					if (isAssigns) {
						if (targetBehavior.assignsNothing())
							throw new CIVLSyntaxException(
									"assigns clause conflicts with previous assigns \\nothing",
									source);
						targetBehavior.addAssignsMemoryUnit(mu);
					} else {
						if (targetBehavior.readsNothing())
							throw new CIVLSyntaxException(
									"reads clause conflicts with previous reads \\nothing",
									source);
						targetBehavior.addReadsMemoryUnit(mu);
					}
				}
			}
			break;
		}
		case ASSUMES: {
			assert targetBehavior instanceof NamedFunctionBehavior;
			Expression expression = translateExpressionNode(
					((AssumesNode) contractNode).getPredicate(), scope, true);
			behavior.addAssumption(expression);
			break;
		}
		case BEHAVIOR: {
			assert behavior == null;
			BehaviorNode behaviorNode = (BehaviorNode) contractNode;
			NamedFunctionBehavior namedBehavior = this.contractFactory
					.newNamedFunctionBehavior(source, behaviorNode.getName()
							.name());
			SequenceNode<ContractNode> body = behaviorNode.getBody();

			for (ContractNode item : body) {
				this.translateContractNodeWork(item, null, collectiveBehavior,
						namedBehavior);
			}
			if (collectiveBehavior != null)
				collectiveBehavior.addNamedBehaviors(namedBehavior);
			else
				functionContract.addNamedBehavior(namedBehavior);
			break;
		}

		case DEPENDS: {
			DependsNode dependsNode = (DependsNode) contractNode;
			SequenceNode<DependsEventNode> eventNodes = dependsNode
					.getEventList();

			for (DependsEventNode eventNode : eventNodes) {
				DependsEvent event = this.translateDependsEvent(eventNode,
						scope);

				if (event.dependsEventKind() == DependsEventKind.NOACT) {
					if (targetBehavior.numDependsEvents() > 0)
						throw new CIVLSyntaxException(
								"depends \\noact conflicts with previous depends clause",
								source);
					targetBehavior.setDependsNoact();
				} else if (event.dependsEventKind() == DependsEventKind.ANYACT) {
					if (targetBehavior.dependsNoact())
						throw new CIVLSyntaxException(
								"depends \\anyact conflicts with previous depends \\noact clause",
								source);
					targetBehavior.setDependsAnyact();
				} else
					targetBehavior.addDependsEvent(event);
			}
			if (targetBehavior.dependsAnyact())
				targetBehavior.clearDependsEvents();
			break;
		}
		case ENSURES: {
			currentContractKind = ContractKind.ENSURES;
			Expression expression = translateExpressionNode(
					((EnsuresNode) contractNode).getExpression(), scope, true);
			targetBehavior.addPostcondition(expression);
			currentContractKind = null;
			break;
		}
		case REQUIRES: {
			currentContractKind = ContractKind.REQUIRES;
			Expression expression = translateExpressionNode(
					((RequiresNode) contractNode).getExpression(), scope, true);
			targetBehavior.addPrecondition(expression);
			currentContractKind = null;
			break;
		}
		case GUARDS: {
			Expression guard = this.translateExpressionNode(
					((GuardsNode) contractNode).getExpression(), scope, true);

			functionContract.setGuard(guard);
			break;
		}
		case MPI_COLLECTIVE:
			MPICollectiveBehavior newCollectiveBehavior;

			currentMPICommunicator = translateExpressionNode(
					((MPICollectiveBlockNode) contractNode).getMPIComm(),
					scope, true);
			newCollectiveBehavior = translateMPICollectiveBehavior(
					(MPICollectiveBlockNode) contractNode, scope,
					functionContract);
			currentMPICommunicator = null;
			functionContract.addMPICollectiveBehavior(newCollectiveBehavior);
			break;
		case PURE:
			functionContract.setPure(true);
			break;
		case COMPLETENESS:
		default:
			throw new CIVLUnimplementedFeatureException(
					"Translate Procedure ContractNode with "
							+ contractNode.contractKind());
		}
	}

	private DependsEvent translateDependsEvent(DependsEventNode eventNode,
			Scope scope) {
		DependsEventNodeKind kind = eventNode.getEventKind();
		CIVLSource source = this.modelFactory.sourceOf(eventNode);

		switch (kind) {
		case MEMORY: {
			MemoryEventNode readWriteEvent = (MemoryEventNode) eventNode;
			Set<Expression> muSet = new HashSet<>();
			SequenceNode<ExpressionNode> muNodeSet = readWriteEvent
					.getMemoryList();

			for (ExpressionNode muNode : muNodeSet) {
				muSet.add(this.translateExpressionNode(muNode, scope, true));
			}
			if (readWriteEvent.isRead())
				return this.contractFactory.newReadEvent(source, muSet);
			else
				return this.contractFactory.newWriteEvent(source, muSet);
		}
		case CALL: {
			CallEventNode callEvent = (CallEventNode) eventNode;
			Pair<Function, CIVLFunction> functionPair = this
					.getFunction(callEvent.getFunction());
			SequenceNode<ExpressionNode> argumentNodes = callEvent.arguments();
			List<Expression> arguments = new ArrayList<>();
			CallEvent call;

			for (ExpressionNode argNode : argumentNodes) {
				arguments.add(this
						.translateExpressionNode(argNode, scope, true));
			}
			call = this.contractFactory.newCallEvent(source,
					functionPair.right, arguments);
			if (functionPair.right == null)
				this.modelBuilder.callEvents.put(call, functionPair.left);
			return call;
		}
		case COMPOSITE: {
			CompositeEventNode compositeEvent = (CompositeEventNode) eventNode;
			CompositeEventOperator operator;
			DependsEvent left, right;

			switch (compositeEvent.eventOperator()) {
			case UNION:
				operator = CompositeEventOperator.UNION;
				break;
			case DIFFERENCE:
				operator = CompositeEventOperator.DIFFERENCE;
				break;
			case INTERSECT:
				operator = CompositeEventOperator.INTERSECT;
				break;
			default:
				throw new CIVLUnimplementedFeatureException(
						"unknown kind of composite event operatore: "
								+ compositeEvent.eventOperator(), source);
			}
			left = this.translateDependsEvent(compositeEvent.getLeft(), scope);
			right = this
					.translateDependsEvent(compositeEvent.getRight(), scope);
			return this.contractFactory.newCompositeEvent(source, operator,
					left, right);
		}
		case ANYACT:
			return this.contractFactory.newAnyactEvent(source);
		case NOACT:
			return this.contractFactory.newNoactEvent(source);
		default:
			throw new CIVLUnimplementedFeatureException(
					"unknown kind of depends event: " + kind, source);
		}

	}

	@Override
	protected Expression translateExpressionNode(ExpressionNode expressionNode,
			Scope scope, boolean translateConversions) {
		ExpressionKind kind = expressionNode.expressionKind();
		CIVLSource source = this.modelFactory.sourceOf(expressionNode);

		switch (kind) {
		case MPI_CONTRACT_EXPRESSION:
			return translateMPIContractExpression(
					(MPIContractExpressionNode) expressionNode, scope);
		case NOTHING: {
			return this.modelFactory.nothing(source);
		}
		case WILDCARD: {
			return this.modelFactory.wildcardExpression(
					source,
					this.translateABCType(source, scope,
							expressionNode.getConvertedType()));
		}
		default:
			return super.translateExpressionNode(expressionNode, scope,
					translateConversions);
		}
	}

	/**
	 * Translate a {@link MPIContractExpressionNode} into a CIVL Expression
	 * 
	 * @param node
	 * @param scope
	 * @return
	 */
	private Expression translateMPIContractExpression(
			MPIContractExpressionNode node, Scope scope) {
		MPIContractExpressionKind kind = node.MPIContractExpressionKind();
		MPI_CONTRACT_EXPRESSION_KIND civlMpiContractKind = null;
		int numArgs = 0;

		switch (kind) {
		case MPI_INTEGER_CONSTANT:
			return translateMPIIntegerConstantNode(
					(CommonMPIConstantNode) node, scope);
		case MPI_EMPTY_IN:
			civlMpiContractKind = MPI_CONTRACT_EXPRESSION_KIND.MPI_EMPTY_IN;
			numArgs = 1;
			break;
		case MPI_EMPTY_OUT:
			civlMpiContractKind = MPI_CONTRACT_EXPRESSION_KIND.MPI_EMPTY_OUT;
			numArgs = 1;
			break;
		case MPI_EQUALS:
			civlMpiContractKind = MPI_CONTRACT_EXPRESSION_KIND.MPI_EQUALS;
			numArgs = 2;
			break;
		case MPI_REGION:
			civlMpiContractKind = MPI_CONTRACT_EXPRESSION_KIND.MPI_REGION;
			numArgs = 3;
			break;
		case MPI_SIZE:
			civlMpiContractKind = MPI_CONTRACT_EXPRESSION_KIND.MPI_SIZE;
			numArgs = 4;
			break;
		}
		if (currentMPICommunicator == null) {
			throw new CIVLSyntaxException("MPI Contract expression: "
					+ civlMpiContractKind
					+ " can only be used in MPI collective behaviors");
		}
		assert numArgs > 0 && civlMpiContractKind != null;

		Expression[] arguments = new Expression[numArgs];

		for (int i = 0; i < numArgs; i++)
			arguments[i] = this.translateExpressionNode(node.getArgument(i),
					scope, true);
		return modelFactory.mpiContractExpression(modelFactory.sourceOf(node),
				scope, currentMPICommunicator, arguments, civlMpiContractKind);

	}

	private Expression translateMPIIntegerConstantNode(
			CommonMPIConstantNode node, Scope scope) {
		MPIConstantKind kind = node.getMPIConstantKind();
		CIVLSource source = modelFactory.sourceOf(node);
		Identifier variableIdent;
		Variable result;

		switch (kind) {
		case MPI_COMM_RANK:
			variableIdent = modelFactory.identifier(source,
					contractMPICommRankName);
			break;
		case MPI_COMM_SIZE:
			variableIdent = modelFactory.identifier(source,
					contractMPICommSizeName);
			break;
		default:
			throw new CIVLInternalException("Unreachable", (CIVLSource) null);
		}
		if (!scope.containsVariable(variableIdent.name())) {
			result = modelFactory.variable(source, modelFactory.typeFactory()
					.integerType(), variableIdent, scope.numVariables());
			scope.addVariable(result);
			result.setScope(scope);
		} else
			result = scope.variable(variableIdent);
		return modelFactory.variableExpression(source, result);
	}

	@Override
	protected Expression translateResultNode(ResultNode resultNode, Scope scope) {
		CIVLSource resultSource = modelFactory.sourceOf(resultNode);
		Variable resultVariable;
		Identifier resultIdentifier = modelFactory.identifier(resultSource,
				contractResultName);

		if (!scope.containsVariable(contractResultName)) {
			CIVLType resultType = this.translateABCType(resultSource, scope,
					resultNode.getType());

			resultVariable = modelFactory.variable(resultSource, resultType,
					resultIdentifier, scope.numVariables());
			scope.addVariable(resultVariable);
			resultVariable.setScope(scope);
		} else
			resultVariable = scope.variable(resultIdentifier);
		return modelFactory.variableExpression(resultSource, resultVariable);
	}

	/**
	 * Overrding the implementation of VALID operator and PLUS for pointer range
	 * addition.
	 * 
	 * <p>
	 * Valid operator stands for the ACSL constructor "\valid" which takes a
	 * {@link MemExpression} as an argument.
	 * </p>
	 * <p>
	 * The result of addition of a pointer and a range will be a
	 * {@link MemExpression}
	 * </p>
	 */
	@Override
	protected Expression translateOperatorNode(OperatorNode operatorNode,
			Scope scope) {
		Operator op = operatorNode.getOperator();

		switch (op) {
		case VALID:
			Expression arg = translateExpressionNode(
					operatorNode.getArgument(0), scope, true);
			return translateValidOperator(modelFactory.sourceOf(operatorNode),
					arg, scope);
		case PLUS:
			ExpressionNode arg0,
			arg1;

			arg0 = operatorNode.getArgument(0);
			arg1 = operatorNode.getArgument(1);
			if (arg0.expressionKind().equals(ExpressionKind.REGULAR_RANGE)
					|| arg1.expressionKind().equals(
							ExpressionKind.REGULAR_RANGE))
				return translatePointerSet(modelFactory.sourceOf(operatorNode),
						this.translateExpressionNode(arg0, scope, true),
						this.translateExpressionNode(arg1, scope, true),
						BINARY_OPERATOR.PLUS, scope);
			else
				return super.translateOperatorNode(operatorNode, scope);
		default:
			return super.translateOperatorNode(operatorNode, scope);
		}
	}

	/**
	 * Translate an operation which is a pointer add a range into an
	 * {@link MemExpression}
	 * 
	 * @param source
	 *            The CIVLSource of the operation expression
	 * @param arg0
	 *            One of the operand
	 * @param arg1
	 *            One of the operand
	 * @param op
	 *            BINARY_OPERATOR, can be either PLUS or MINUS
	 * @param scope
	 * @return
	 */
	private Expression translatePointerSet(CIVLSource source, Expression arg0,
			Expression arg1, BINARY_OPERATOR op, Scope scope) {
		Expression result, pointer, range;

		if (arg0.getExpressionType().isPointerType()) {
			pointer = arg0;
			range = arg1;
		} else {
			assert arg1.getExpressionType().isPointerType();
			pointer = arg1;
			range = arg0;
		}
		// TODO:LHSExpression
		result = modelFactory.pointerSetExpression(source, scope,
				(LHSExpression) pointer, range);
		return result;
	}

	/**
	 * Translate an valid operation into an {@link UnaryExpression}
	 * 
	 * @param source
	 *            The CIVLSource of the valid operation
	 * @param arg
	 *            The operand of the valid operation
	 * @param scope
	 * @return
	 */
	private Expression translateValidOperator(CIVLSource source,
			Expression arg, Scope scope) {
		PointerSetExpression mem;
		UnaryExpression result;

		// TODO: check if pointer is LHSExpression:
		// \valid operator syntactically accepts either [pointer + range] or
		// [pointer]:
		if (arg.getExpressionType().isPointerType()) {
			if (arg instanceof LHSExpression)
				mem = modelFactory.pointerSetExpression(arg.getSource(), scope,
						(LHSExpression) arg, null);
			else
				throw new CIVLUnimplementedFeatureException(
						"Singleton pointer set but the element is not a LHSExpression.");
		} else
			mem = (PointerSetExpression) arg;
		result = modelFactory
				.unaryExpression(source, UNARY_OPERATOR.VALID, mem);
		if (currentContractKind == ContractKind.REQUIRES) {
			// This \valid expression may be a consequence of requirements:
			int mallocId = modelBuilder.mallocStatements.size();
			LHSExpression memPointer = mem.getBasePointer();
			CIVLType staticElementType = ((CIVLPointerType) mem
					.getBasePointer().getExpressionType()).baseType();

			// TODO: what if pointer is void *?
			modelBuilder.mallocStatements.add(modelFactory.mallocStatement(
					source, null, memPointer, staticElementType, null,
					mem.getRange(), mallocId, null));

			function.addPossibleValidConsequence(new Pair<>(result, mallocId));
		}
		return result;
	}

	/**
	 * Translate a {@link MPICollectiveBlockNode} to a
	 * {@link MPICollectiveBehavior}.
	 * 
	 * @param node
	 * @param scope
	 * @return
	 */
	private MPICollectiveBehavior translateMPICollectiveBehavior(
			MPICollectiveBlockNode node, Scope scope,
			FunctionContract functionContract) {
		MPICollectiveBehavior result;
		CIVLSource source = modelFactory.sourceOf(node);
		Iterator<ContractNode> bodyNodesIter = node.getBody().iterator();
		Expression communicator = translateExpressionNode(node.getMPIComm(),
				scope, true);

		switch (node.getCollectiveKind()) {
		case P2P:
			result = contractFactory.newMPICollectiveBehavior(source,
					communicator, MPICommunicationPattern.P2P);
			break;
		case COL:
			result = contractFactory.newMPICollectiveBehavior(source,
					communicator, MPICommunicationPattern.COL);
			break;
		default:
			throw new CIVLSyntaxException("Unsupported MPI Collective kind: "
					+ node.getCollectiveKind());
		}
		while (bodyNodesIter.hasNext())
			translateContractNodeWork(bodyNodesIter.next(), functionContract,
					result, null);
		return result;
	}
}
