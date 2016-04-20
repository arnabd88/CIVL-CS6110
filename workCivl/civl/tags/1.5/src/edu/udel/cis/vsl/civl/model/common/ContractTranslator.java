package edu.udel.cis.vsl.civl.model.common;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import edu.udel.cis.vsl.abc.ast.entity.IF.Function;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.ContractNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.EnsuresNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.RequiresNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.CollectiveExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode.ExpressionKind;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ResultNode;
import edu.udel.cis.vsl.civl.model.IF.AbstractFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLTypeFactory;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression.BINARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.ContractClauseExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ContractClauseExpression.ContractKind;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.SystemFunctionCallExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public class ContractTranslator extends FunctionTranslator {
	/**
	 * The string type name of the Result Expression:<br>
	 * An special expression used to represent the result of a function in
	 * function contracts.
	 */
	public static final String contractResultName = "$result";

	private CIVLFunction function;

	private ModelFactory modelFactory;

	private CIVLTypeFactory typeFactory;

	private ModelBuilderWorker modelBuilder;

	private Expression processesGroup;

	/******************** Constructor ********************/
	ContractTranslator(ModelBuilderWorker modelBuilder,
			ModelFactory modelFactory, CIVLTypeFactory typeFactory,
			CIVLFunction function) {
		super(modelBuilder, modelFactory, function);
		this.modelFactory = modelFactory;
		this.typeFactory = typeFactory;
		this.modelBuilder = modelBuilder;
		this.function = function;
	}

	/**
	 * Translates a {@link ContractNode} to a {@link ContractClauseExpression}.
	 * 
	 * @param contractNode
	 * @return
	 */
	public ContractClauseExpression translateContractNode(
			ContractNode contractNode) {
		ContractClauseExpression clause;
		ExpressionNode contractExpressionNode;
		ContractKind kind;

		// A processesGroup is associated to a contractNode, each time
		// processing a new contractNode, reset the global field of
		// processesGroup, ditto for contractCalls:
		processesGroup = null;
		switch (contractNode.contractKind()) {
		case ENSURES:
			contractExpressionNode = ((EnsuresNode) contractNode)
					.getExpression();
			kind = ContractKind.ENSURES;
			break;
		case REQUIRES:
			contractExpressionNode = ((RequiresNode) contractNode)
					.getExpression();
			kind = ContractKind.REQUIRES;
			break;
		default:
			throw new CIVLUnimplementedFeatureException(
					"Translate Procedure ContractNode with "
							+ contractNode.contractKind());
		}
		clause = translateContractExpressionNode(contractExpressionNode,
				function.outerScope(), modelFactory.sourceOf(contractNode),
				kind);
		return clause;
	}

	/**
	 * Merging {@link ContractClauseExpression}s by calling the helper function:
	 * {@link #mergeSingleKindContracts(List, CIVLTypeFactory, ModelFactory)}.
	 * This function pre-processes contracts according to their
	 * {@link ContractKind}, then calls the helper function.
	 * 
	 * @param contracts
	 *            The {@link List} of unmegred contracts
	 * @param typeFactory
	 *            A reference to a {@link CIVLTypeFactory} instance
	 * @param modelFactory
	 *            A reference to a {@link ModelFactory} instance
	 * @return
	 */
	static public CIVLFunction mergeContracts(
			List<ContractClauseExpression> contracts,
			CIVLTypeFactory typeFactory, ModelFactory modelFactory,
			CIVLFunction function) {
		List<ContractClauseExpression> requires, ensures;

		requires = new LinkedList<>();
		ensures = new LinkedList<>();
		for (ContractClauseExpression contract : contracts) {
			ContractKind kind = contract.contractKind();

			if (kind.equals(ContractKind.REQUIRES))
				requires.add(contract);
			else if (kind.equals(ContractKind.ENSURES))
				ensures.add(contract);
			else
				throw new CIVLUnimplementedFeatureException(
						"Merge contract with kind " + contract.contractKind());
		}
		for (ContractClauseExpression precond : mergeSingleKindContracts(
				requires, typeFactory, modelFactory))
			function.addPrecondition(precond);
		for (ContractClauseExpression postcond : mergeSingleKindContracts(
				ensures, typeFactory, modelFactory))
			function.addPostcondition(postcond);
		return function;
	}

	/**
	 * Merging {@link ContractClauseExpression}s with same {@link ContractKind}
	 * together according to following rules: <br>
	 * 1. collective contracts shouldn't be merged with non-collective
	 * contracts;<br>
	 * 
	 * 2. collective contracts should be merged according to their collective
	 * group;<br>
	 * 
	 * @param contracts
	 *            The {@link List} of unmegred contracts
	 * @param typeFactory
	 *            A reference to a {@link CIVLTypeFactory} instance
	 * @param modelFactory
	 *            A reference to a {@link ModelFactory} instance
	 * @return
	 */
	static private List<ContractClauseExpression> mergeSingleKindContracts(
			List<ContractClauseExpression> contracts,
			CIVLTypeFactory typeFactory, ModelFactory modelFactory) {
		Map<Variable, Integer> collectiveGroup = new HashMap<>();
		ArrayList<ContractClauseExpression> collectiveContracts = new ArrayList<>();
		ContractClauseExpression regularContracts = null;
		CIVLType contractType = typeFactory.booleanType();

		for (ContractClauseExpression contract : contracts) {
			ContractKind kind = contract.contractKind();
			CIVLSource contractBodySource = contract.getBody().getSource();
			CIVLSource contractSource = contract.getSource();

			// Collective contracts should be merged with their groups:
			if (contract.isCollectiveClause()) {
				ContractClauseExpression canocContract;
				int collectContractIdx;
				VariableExpression group = (VariableExpression) contract
						.getCollectiveGroup();

				if (!collectiveGroup.containsKey(group.variable())) {
					collectContractIdx = collectiveContracts.size();
					collectiveGroup.put(group.variable(), collectContractIdx);
					canocContract = modelFactory.contractClauseExpression(
							contract.getSource(), contractType, group,
							contract.getBody(), kind);
					collectiveContracts.add(canocContract);
				} else {
					Expression mergedBody;

					collectContractIdx = collectiveGroup.get(group.variable());
					canocContract = collectiveContracts.get(collectContractIdx);
					mergedBody = canocContract.getBody();
					mergedBody = modelFactory
							.binaryExpression(modelFactory.sourceOfSpan(
									mergedBody.getSource(), contract.getBody()
											.getSource()), BINARY_OPERATOR.AND,
									mergedBody, contract.getBody());
					canocContract = modelFactory.contractClauseExpression(
							modelFactory.sourceOfSpan(
									canocContract.getSource(), contractSource),
							contractType, group, mergedBody, kind);
					collectiveContracts.set(collectContractIdx, canocContract);
				}
			}
			// Regular contracts should be merged together:
			else {
				Expression oldBody;

				if (regularContracts != null) {
					oldBody = regularContracts.getBody();
					oldBody = modelFactory.binaryExpression(modelFactory
							.sourceOfSpan(oldBody.getSource(),
									contractBodySource), BINARY_OPERATOR.AND,
							oldBody, contract.getBody());
					regularContracts = modelFactory.contractClauseExpression(
							modelFactory.sourceOfSpan(
									regularContracts.getSource(),
									contractSource), contractType, null,
							oldBody, kind);
				} else
					regularContracts = contract;
			}
		}
		if (regularContracts != null)
			collectiveContracts.add(regularContracts);
		collectiveGroup.clear();
		return collectiveContracts;
	}

	@Override
	protected Expression translateFunctionCallExpression(
			FunctionCallNode callNode, Scope scope) {
		Expression result;
		ExpressionNode functionExpression = callNode.getFunction();
		Function callee;
		CIVLFunction civlFunction;
		String functionName;
		CIVLSource source = modelFactory.sourceOf(callNode);

		if (functionExpression instanceof IdentifierExpressionNode) {
			callee = (Function) ((IdentifierExpressionNode) functionExpression)
					.getIdentifier().getEntity();
		} else
			throw new CIVLUnimplementedFeatureException(
					"Function call must use identifier for now: "
							+ functionExpression.getSource());
		civlFunction = modelBuilder.functionMap.get(callee);
		functionName = civlFunction.name().name();
		assert civlFunction != null;
		if (civlFunction instanceof AbstractFunction) {
			List<Expression> arguments = new ArrayList<Expression>();

			for (int i = 0; i < callNode.getNumberOfArguments(); i++) {
				Expression actual = translateExpressionNode(
						callNode.getArgument(i), scope, true);

				actual = arrayToPointer(actual);
				arguments.add(actual);
			}
			result = modelFactory.abstractFunctionCallExpression(
					modelFactory.sourceOf(callNode),
					(AbstractFunction) civlFunction, arguments);
			return result;
		} else if (civlFunction.isSystemFunction()) {
			/*
			 * Following system functions can be used as expressions in
			 * contract:
			 */
			switch (functionName) {
			case "$mpi_isRecvBufEmpty":
			case "$mpi_isSendBufEmpty":
				return this.transformContractCall(civlFunction, scope,
						callNode, source);
			default:
			}
		}
		throw new CIVLUnimplementedFeatureException("Using function call: "
				+ functionName + "as expression in contract.");
	}

	/**
	 * Transform contract message buffer calls:
	 * 
	 * <code>collective(group) $mpi_isRecvBufEmpty(x) ==> $mpi_isRecvBufEmpty(x,
	 * group)</code> (ditto for other contract message buffer functions)
	 * 
	 * @param civlFunction
	 *            The {@link CIVLFunction} of the contract message buffer
	 *            function
	 * @param scope
	 *            The scope to where the contract message buffer belongs
	 * @param callNode
	 *            The {@link The FunctionCallNode} of the function call
	 * @param source
	 *            The CIVLSource of the function call
	 * @return
	 */
	private Expression transformContractCall(CIVLFunction civlFunction,
			Scope scope, FunctionCallNode callNode, CIVLSource source) {
		// A location only be used to construct a systemCallExpression,
		// it doesn't have income statements
		// and the outgoing statement dosen't have target:
		Location floatingLocation;
		List<Expression> arguments = new LinkedList<>();
		Expression functionExpr = modelFactory.functionIdentifierExpression(
				source, civlFunction);
		Expression arg;
		CallOrSpawnStatement civlSysFunctionCall;
		SystemFunctionCallExpression result;
		String functionName = civlFunction.name().name();

		floatingLocation = modelFactory.location(source, scope);
		for (ExpressionNode argNode : callNode.getArguments()) {
			argNode = callNode.getArgument(0);
			arg = translateExpressionNode(argNode, scope, true);
			arguments.add(arg);
		}
		// Add Collective Group as the second argument
		assert processesGroup != null : "Building model for " + functionName
				+ "() but there is no collective group information";
		arguments.add(processesGroup);
		civlSysFunctionCall = modelFactory.callOrSpawnStatement(source,
				floatingLocation, true, functionExpr, arguments,
				modelFactory.trueExpression(null));
		result = modelFactory.systemFunctionCallExpression(civlSysFunctionCall);
		return result;
	}

	/**
	 * Translates an {@link ExpressionNode} to {@link ContractClauseExpression}
	 * 
	 * @param expressionNode
	 *            The ExpressionNode which should be a child of a
	 *            {@link ContractNode}
	 * @param scope
	 *            The scope to where the contract clause belongs
	 * @param source
	 *            The CIVLSource of the contract clasue expression
	 * @param kind
	 *            The {@link ContractKind} of the contract
	 * @return
	 */
	private ContractClauseExpression translateContractExpressionNode(
			ExpressionNode expressionNode, Scope scope, CIVLSource source,
			ContractKind kind) {
		ExpressionNode bodyNode, procsGroupNode;
		Expression body;

		if (expressionNode.expressionKind().equals(ExpressionKind.COLLECTIVE)) {
			bodyNode = ((CollectiveExpressionNode) expressionNode).getBody();
			procsGroupNode = ((CollectiveExpressionNode) expressionNode)
					.getProcessesGroupExpression();
		} else {
			bodyNode = expressionNode;
			procsGroupNode = null;
		}
		if (procsGroupNode != null)
			processesGroup = translateExpressionNode(procsGroupNode, scope,
					true);
		body = translateExpressionNode(bodyNode, scope, true);
		return modelFactory.contractClauseExpression(source,
				this.typeFactory.booleanType(), processesGroup, body, kind);
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
}
