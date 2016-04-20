/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Vector;

import edu.udel.cis.vsl.abc.ast.entity.IF.Entity;
import edu.udel.cis.vsl.abc.ast.entity.IF.Label;
import edu.udel.cis.vsl.abc.ast.entity.IF.OrdinaryEntity;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.ContractNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.EnsuresNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FieldDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.InitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.RequiresNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.TypedefDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.CastNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IntegerConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ResultNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.SelfNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.SpawnNode;
import edu.udel.cis.vsl.abc.ast.node.IF.label.LabelNode;
import edu.udel.cis.vsl.abc.ast.node.IF.label.OrdinaryLabelNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.AssertNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.AssumeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ChooseStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CompoundStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.DeclarationListNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ExpressionStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ForLoopInitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ForLoopNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.GotoNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.IfNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.LabeledStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.NullStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ReturnNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.WaitNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.WhenNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.ArrayTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.BasicTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.FunctionTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.PointerTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.StructureOrUnionTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode.TypeNodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypedefNameNode;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType;
import edu.udel.cis.vsl.abc.ast.type.IF.Type.TypeKind;
import edu.udel.cis.vsl.abc.ast.unit.IF.TranslationUnit;
import edu.udel.cis.vsl.civl.model.IF.Function;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.ModelBuilder;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.SystemFunction;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression.BINARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.IntegerLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.LiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.StringLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression.UNARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.CallStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ReturnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.type.ArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.StructField;
import edu.udel.cis.vsl.civl.model.IF.type.Type;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * Class to provide translation from an AST to a model.
 * 
 * @author zirkeltk
 * 
 */
public class CommonModelBuilder implements ModelBuilder {

	private ModelFactory factory;
	private Vector<FunctionDefinitionNode> unprocessedFunctions;
	private Map<FunctionDefinitionNode, Scope> containingScopes;
	private Map<CallStatement, FunctionDefinitionNode> callStatements;
	private Map<FunctionDefinitionNode, Function> functionMap;
	private Map<LabelNode, Location> labeledLocations;
	private Map<Statement, LabelNode> gotoStatements;
	private Map<String, Type> typedefMap;
	private Map<String, Function> systemFunctions;

	/**
	 * The model builder translates the AST into a CIVL model.
	 */
	public CommonModelBuilder() {
		factory = new CommonModelFactory();
		setUpSystemFunctions();
	}

	private void setUpSystemFunctions() {
		SystemFunction malloc = factory.systemFunction(factory
				.identifier("malloc"));
		SystemFunction free = factory
				.systemFunction(factory.identifier("free"));
		SystemFunction printf = factory.systemFunction(factory
				.identifier("printf"));

		malloc.setLibrary("civlc");
		free.setLibrary("civlc");
		printf.setLibrary("civlc");
		systemFunctions = new LinkedHashMap<String, Function>();
		systemFunctions.put("malloc", malloc);
		systemFunctions.put("free", free);
		systemFunctions.put("printf", printf);
	}

	/**
	 * @return The model factory used by this model builder.
	 */
	public ModelFactory factory() {
		return factory;
	}

	/**
	 * Build the model.
	 * 
	 * @param unit
	 *            The translation unit for the AST.
	 * @return The model.
	 */
	public Model buildModel(TranslationUnit unit) {
		Model model;
		Identifier systemID = factory.identifier("_CIVL_system");
		Function system = factory.function(systemID, new Vector<Variable>(),
				null, null, null);
		ASTNode rootNode = unit.getRootNode();
		Location returnLocation;
		Statement returnStatement;
		FunctionDefinitionNode mainFunction = null;
		Statement mainBody;
		Vector<Statement> initializations = new Vector<Statement>();

		containingScopes = new LinkedHashMap<FunctionDefinitionNode, Scope>();
		callStatements = new LinkedHashMap<CallStatement, FunctionDefinitionNode>();
		functionMap = new LinkedHashMap<FunctionDefinitionNode, Function>();
		unprocessedFunctions = new Vector<FunctionDefinitionNode>();
		typedefMap = new LinkedHashMap<String, Type>();
		for (int i = 0; i < rootNode.numChildren(); i++) {
			ASTNode node = rootNode.child(i);

			if (node instanceof VariableDeclarationNode) {
				InitializerNode init = ((VariableDeclarationNode) node)
						.getInitializer();

				processVariableDeclaration(system.outerScope(),
						(VariableDeclarationNode) rootNode.child(i));
				if (init != null) {
					Expression left;
					Expression right;
					Location location = factory.location(system.outerScope());

					left = factory
							.variableExpression(system
									.outerScope()
									.getVariable(
											system.outerScope().numVariables() - 1));
					right = expression((ExpressionNode) init,
							system.outerScope());
					if (!initializations.isEmpty()) {
						initializations.lastElement().setTarget(location);
					}
					initializations.add(factory.assignStatement(location, left,
							right));
					system.addLocation(location);
					system.addStatement(initializations.lastElement());
				}
			} else if (node instanceof FunctionDefinitionNode) {
				if (((FunctionDefinitionNode) node).getName().equals("main")) {
					mainFunction = (FunctionDefinitionNode) node;
				} else {
					unprocessedFunctions.add((FunctionDefinitionNode) node);
					containingScopes.put((FunctionDefinitionNode) node,
							system.outerScope());
				}
			} else if (node instanceof FunctionDeclarationNode) {
				// Do we need to keep track of these for any reason?
			} else if (node instanceof TypedefDeclarationNode) {
				String typeName = ((TypedefDeclarationNode) node).getName();

				if (typeName.equals("$proc")) {
					typedefMap.put(typeName, factory.processType());
				} else if (typeName.equals("$heap")) {
					typedefMap.put(typeName, factory.heapType());
				} else {
					typedefMap.put(typeName,
							processType(((TypedefDeclarationNode) node)
									.getTypeNode()));
				}
			} else {
				throw new RuntimeException("Unsupported declaration type: "
						+ node);
			}
		}
		if (mainFunction == null) {
			throw new RuntimeException("Program must have a main function.");
		}
		labeledLocations = new LinkedHashMap<LabelNode, Location>();
		gotoStatements = new LinkedHashMap<Statement, LabelNode>();
		if (!initializations.isEmpty()) {
			system.setStartLocation(initializations.firstElement().source());
			mainBody = statement(system, initializations.lastElement(),
					mainFunction.getBody(), system.outerScope());
		} else {
			mainBody = statement(system, null, mainFunction.getBody(),
					system.outerScope());
		}
		if (!(mainBody instanceof ReturnStatement)) {
			returnLocation = factory.location(system.outerScope());
			returnStatement = factory.returnStatement(returnLocation, null);
			if (mainBody != null) {
				mainBody.setTarget(returnLocation);
			} else {
				system.setStartLocation(returnLocation);
			}
			system.addLocation(returnLocation);
			system.addStatement(returnStatement);
		}
		model = factory.model(system);
		while (!unprocessedFunctions.isEmpty()) {
			FunctionDefinitionNode functionDefinition = unprocessedFunctions
					.remove(0);
			Function newFunction = processFunction(functionDefinition,
					containingScopes.get(functionDefinition));
			SequenceNode<ContractNode> contract = functionDefinition
					.getContract();
			Expression precondition = null;
			Expression postcondition = null;

			if (contract != null) {
				for (int i = 0; i < contract.numChildren(); i++) {
					ContractNode contractComponent = contract
							.getSequenceChild(i);
					Expression componentExpression;

					if (contractComponent instanceof EnsuresNode) {
						componentExpression = expression(
								((EnsuresNode) contractComponent)
										.getExpression(),
								newFunction.outerScope());
						if (postcondition == null) {
							postcondition = componentExpression;
						} else {
							postcondition = factory.binaryExpression(
									BINARY_OPERATOR.AND, postcondition,
									componentExpression);
						}
					} else {
						componentExpression = expression(
								((RequiresNode) contractComponent)
										.getExpression(),
								newFunction.outerScope());
						if (precondition == null) {
							precondition = componentExpression;
						} else {
							precondition = factory.binaryExpression(
									BINARY_OPERATOR.AND, precondition,
									componentExpression);
						}
					}
				}
			}
			if (precondition != null) {
				newFunction.setPrecondition(precondition);
			}
			if (postcondition != null) {
				newFunction.setPostcondition(postcondition);
			}
			model.addFunction(newFunction);
			functionMap.put(functionDefinition, newFunction);
		}
		for (CallStatement statement : callStatements.keySet()) {
			statement
					.setFunction(functionMap.get(callStatements.get(statement)));
		}
		for (Statement s : gotoStatements.keySet()) {
			s.setTarget(labeledLocations.get(gotoStatements.get(s)));
		}
		return model;
	}

	private Function processFunction(FunctionDefinitionNode functionNode,
			Scope scope) {
		Function result;
		Identifier name = factory.identifier(functionNode.getName());
		Vector<Variable> parameters = new Vector<Variable>();
		FunctionTypeNode functionTypeNode = functionNode.getTypeNode();
		Type returnType = processType(functionTypeNode.getReturnType());
		Statement body;

		labeledLocations = new LinkedHashMap<LabelNode, Location>();
		gotoStatements = new LinkedHashMap<Statement, LabelNode>();
		for (int i = 0; i < functionTypeNode.getParameters().numChildren(); i++) {
			Type type = processType(functionTypeNode.getParameters()
					.getSequenceChild(i).getTypeNode());
			Identifier variableName = factory.identifier(functionTypeNode
					.getParameters().getSequenceChild(i).getName());

			parameters.add(factory.variable(type, variableName,
					parameters.size()));
		}
		result = factory.function(name, parameters, returnType, scope, null);
		body = statement(result, null, functionNode.getBody(),
				result.outerScope());
		if (!(body instanceof ReturnStatement)) {
			Location returnLocation = factory.location(result.outerScope());
			ReturnStatement returnStatement = factory.returnStatement(
					returnLocation, null);

			body.setTarget(returnLocation);
			result.addLocation(returnLocation);
			result.addStatement(returnStatement);
		}
		for (Statement s : gotoStatements.keySet()) {
			s.setTarget(labeledLocations.get(gotoStatements.get(s)));
		}
		return result;
	}

	private void processVariableDeclaration(Scope scope,
			VariableDeclarationNode node) {
		Type type = processType(node.getTypeNode());
		Identifier name = factory.identifier(node.getName());
		Variable variable = factory.variable(type, name, scope.numVariables());

		if (type instanceof ArrayType) {
			ExpressionNode extentNode = ((ArrayTypeNode) node.getTypeNode())
					.getExtent();
			Expression extent;

			if (extentNode != null) {
				extent = expression(extentNode, scope);
				variable.setExtent(extent);
			}
		}
		if (node.getTypeNode().isInputQualified()) {
			variable.setIsExtern(true);
		}
		scope.addVariable(variable);
	}

	private Type processType(TypeNode typeNode) {
		Type result = null;

		// TODO: deal with more types.
		if (typeNode.kind() == TypeNodeKind.BASIC) {
			switch (((BasicTypeNode) typeNode).getBasicTypeKind()) {
			case SHORT:
			case UNSIGNED_SHORT:
			case INT:
			case UNSIGNED:
			case LONG:
			case UNSIGNED_LONG:
			case LONG_LONG:
			case UNSIGNED_LONG_LONG:
				return factory.integerType();
			case FLOAT:
			case DOUBLE:
			case LONG_DOUBLE:
				return factory.realType();
			case BOOL:
				return factory.booleanType();
			case CHAR:
				break;
			case DOUBLE_COMPLEX:
				break;
			case FLOAT_COMPLEX:
				break;
			case LONG_DOUBLE_COMPLEX:
				break;
			case SIGNED_CHAR:
				break;
			case UNSIGNED_CHAR:
				break;
			default:
				break;
			}
		} else if (typeNode.kind() == TypeNodeKind.PROCESS) {
			return factory.processType();
		} else if (typeNode.kind() == TypeNodeKind.ARRAY) {
			return factory.arrayType(processType(((ArrayTypeNode) typeNode)
					.getElementType()));
		} else if (typeNode.kind() == TypeNodeKind.POINTER) {
			return factory.pointerType(processType(((PointerTypeNode) typeNode)
					.referencedType()));
		} else if (typeNode.kind() == TypeNodeKind.TYPEDEF_NAME) {
			return typedefMap
					.get(((TypedefNameNode) typeNode).getName().name());
		} else if (typeNode.kind() == TypeNodeKind.STRUCTURE_OR_UNION) {
			SequenceNode<FieldDeclarationNode> fieldNodes = ((StructureOrUnionTypeNode) typeNode)
					.getStructDeclList();
			List<StructField> fields = new Vector<StructField>();

			for (int i = 0; i < fieldNodes.numChildren(); i++) {
				FieldDeclarationNode fieldNode = fieldNodes.getSequenceChild(i);
				Identifier name = factory.identifier(fieldNode.getName());
				Type type = processType(fieldNode.getTypeNode());

				fields.add(factory.structField(name, type));
			}
			result = factory.structType(fields);
		}
		return result;
	}

	/* *********************************************************************
	 * Expressions
	 * *********************************************************************
	 */

	/**
	 * Translate an expression from the CIVL AST to the CIVL model.
	 * 
	 * @param expression
	 *            The expression being translated.
	 * @param scope
	 *            The (static) scope containing the expression.
	 * @return The model representation of the expression.
	 */
	public Expression expression(ExpressionNode expression, Scope scope) {
		Expression result = null;

		if (expression instanceof OperatorNode) {
			result = operator((OperatorNode) expression, scope);
		} else if (expression instanceof IdentifierExpressionNode) {
			result = variableExpression((IdentifierExpressionNode) expression,
					scope);
		} else if (expression instanceof ConstantNode) {
			result = constant((ConstantNode) expression);
		} else if (expression instanceof ResultNode) {
			result = factory.resultExpression();
		} else if (expression instanceof SelfNode) {
			result = factory.selfExpression();
		} else if (expression instanceof CastNode) {
			result = castExpression((CastNode) expression, scope);
		}
		return result;
	}

	/**
	 * Translate a cast expression from the CIVL AST to the CIVL model.
	 * 
	 * @param expression
	 *            The cast expression.
	 * @param scope
	 *            The (static) scope containing the expression.
	 * @return The model representation of the expression.
	 */
	public Expression castExpression(CastNode expression, Scope scope) {
		Expression result;
		Type castType = processType(expression.getCastType());
		Expression castExpression = expression(expression.getArgument(), scope);

		result = factory.castExpression(castType, castExpression);
		return result;
	}

	/**
	 * Translate an operator expression from the CIVL AST to the CIVL model.
	 * 
	 * @param expression
	 *            The operator expression.
	 * @param scope
	 *            The (static) scope containing the expression.
	 * @return The model representation of the expression.
	 */
	public Expression operator(OperatorNode expression, Scope scope) {
		int numArgs = expression.getNumberOfArguments();
		List<Expression> arguments = new Vector<Expression>();
		Expression result = null;

		for (int i = 0; i < numArgs; i++) {
			arguments.add(expression(expression.getArgument(i), scope));
		}
		// TODO: Bitwise ops, =, {%,/,*,+,-}=, pointer ops, comma, ?
		if (numArgs < 1 || numArgs > 3) {
			throw new RuntimeException("Unsupported number of arguments: "
					+ numArgs + " in expression " + expression);
		}
		switch (expression.getOperator()) {
		case ADDRESSOF:
			result = factory.unaryExpression(UNARY_OPERATOR.ADDRESSOF,
					arguments.get(0));
			break;
		case DEREFERENCE:
			result = factory.unaryExpression(UNARY_OPERATOR.DEREFERENCE,
					arguments.get(0));
			break;
		case CONDITIONAL:
			result = factory.conditionalExpression(arguments.get(0),
					arguments.get(1), arguments.get(2));
			break;
		case DIV:
			result = factory.binaryExpression(BINARY_OPERATOR.DIVIDE,
					arguments.get(0), arguments.get(1));
			break;
		case EQUALS:
			result = factory.binaryExpression(BINARY_OPERATOR.EQUAL,
					arguments.get(0), arguments.get(1));
			break;
		case GT:
			result = factory.binaryExpression(BINARY_OPERATOR.LESS_THAN,
					arguments.get(1), arguments.get(0));
			break;
		case GTE:
			result = factory.binaryExpression(BINARY_OPERATOR.LESS_THAN_EQUAL,
					arguments.get(1), arguments.get(0));
			break;
		case LAND:
			result = factory.binaryExpression(BINARY_OPERATOR.AND,
					arguments.get(0), arguments.get(1));
			break;
		case LOR:
			result = factory.binaryExpression(BINARY_OPERATOR.OR,
					arguments.get(0), arguments.get(1));
			break;
		case LT:
			result = factory.binaryExpression(BINARY_OPERATOR.LESS_THAN,
					arguments.get(0), arguments.get(1));
			break;
		case LTE:
			result = factory.binaryExpression(BINARY_OPERATOR.LESS_THAN_EQUAL,
					arguments.get(0), arguments.get(1));
			break;
		case MINUS:
			result = factory.binaryExpression(BINARY_OPERATOR.MINUS,
					arguments.get(0), arguments.get(1));
			break;
		case MOD:
			result = factory.binaryExpression(BINARY_OPERATOR.MODULO,
					arguments.get(0), arguments.get(1));
			break;
		case NEQ:
			result = factory.binaryExpression(BINARY_OPERATOR.NOT_EQUAL,
					arguments.get(0), arguments.get(1));
			break;
		case NOT:
			result = factory.unaryExpression(UNARY_OPERATOR.NOT,
					arguments.get(0));
			break;
		case PLUS:
			result = factory.binaryExpression(BINARY_OPERATOR.PLUS,
					arguments.get(0), arguments.get(1));
			break;
		case SUBSCRIPT:
			result = factory.arrayIndexExpression(arguments.get(0),
					arguments.get(1));
			break;
		case TIMES:
			result = factory.binaryExpression(BINARY_OPERATOR.TIMES,
					arguments.get(0), arguments.get(1));
			break;
		case UNARYMINUS:
			result = factory.unaryExpression(UNARY_OPERATOR.NEGATIVE,
					arguments.get(0));
			break;
		case UNARYPLUS:
			result = arguments.get(0);
			break;
		default:
			throw new RuntimeException("Unsupported operator: "
					+ expression.getOperator() + " in expression " + expression);
		}
		return result;
	}

	private VariableExpression variableExpression(
			IdentifierExpressionNode identifier, Scope scope) {
		VariableExpression result = null;
		Identifier name = factory.identifier(identifier.getIdentifier().name());

		if (scope.variable(name) == null) {
			throw new RuntimeException("No such variable "
					+ identifier.getSource());
		}
		result = factory.variableExpression(scope.variable(name));
		return result;
	}

	private LiteralExpression constant(ConstantNode constant) {
		LiteralExpression result = null;
		edu.udel.cis.vsl.abc.ast.type.IF.Type convertedType = constant
				.getConvertedType();

		assert convertedType.kind() == TypeKind.BASIC;
		switch (((StandardBasicType) convertedType).getBasicTypeKind()) {
		case SHORT:
		case UNSIGNED_SHORT:
		case INT:
		case UNSIGNED:
		case LONG:
		case UNSIGNED_LONG:
		case LONG_LONG:
		case UNSIGNED_LONG_LONG:
			result = factory.integerLiteralExpression(BigInteger.valueOf(Long
					.parseLong(constant.getStringRepresentation())));
			break;
		case FLOAT:
		case DOUBLE:
		case LONG_DOUBLE:
			result = factory.realLiteralExpression(BigDecimal.valueOf(Double
					.parseDouble(constant.getStringRepresentation())));
			break;
		case BOOL:
			boolean value;

			if (constant instanceof IntegerConstantNode) {
				BigInteger integerValue = ((IntegerConstantNode) constant)
						.getConstantValue().getIntegerValue();

				if (integerValue.intValue() == 0) {
					value = false;
				} else {
					value = true;
				}
			} else {
				value = Boolean
						.parseBoolean(constant.getStringRepresentation());
			}
			result = factory.booleanLiteralExpression(value);
			break;
		default:
			throw new RuntimeException(
					"Unsupported converted type for expression: " + constant);
		}
		return result;
	}

	/* *********************************************************************
	 * Statements
	 * *********************************************************************
	 */

	/**
	 * Takes a statement node and returns the appropriate model statement.
	 * 
	 * @param function
	 *            The function containing this statement.
	 * @param lastStatement
	 *            The previous statement. Null if this is the first statement in
	 *            a function.
	 * @param statement
	 *            The statement node.
	 * @param scope
	 *            The scope containing this statement.
	 * @return The model representation of this statement.
	 */
	private Statement statement(Function function, Statement lastStatement,
			StatementNode statement, Scope scope) {
		Statement result = null;

		if (statement instanceof AssumeNode) {
			result = assume(function, lastStatement, (AssumeNode) statement,
					scope);
		} else if (statement instanceof AssertNode) {
			result = assertStatement(function, lastStatement,
					(AssertNode) statement, scope);
		} else if (statement instanceof ExpressionStatementNode) {
			result = expressionStatement(function, lastStatement,
					(ExpressionStatementNode) statement, scope);
		} else if (statement instanceof CompoundStatementNode) {
			result = compoundStatement(function, lastStatement,
					(CompoundStatementNode) statement, scope);
		} else if (statement instanceof ForLoopNode) {
			result = forLoop(function, lastStatement, (ForLoopNode) statement,
					scope);
		} else if (statement instanceof IfNode) {
			result = ifStatement(function, lastStatement, (IfNode) statement,
					scope);
		} else if (statement instanceof WaitNode) {
			result = wait(function, lastStatement, (WaitNode) statement, scope);
		} else if (statement instanceof NullStatementNode) {
			result = noop(function, lastStatement,
					(NullStatementNode) statement, scope);
		} else if (statement instanceof WhenNode) {
			result = when(function, lastStatement, (WhenNode) statement, scope);
		} else if (statement instanceof ChooseStatementNode) {
			result = choose(function, lastStatement,
					(ChooseStatementNode) statement, scope);
		} else if (statement instanceof GotoNode) {
			result = gotoStatement(function, lastStatement,
					(GotoNode) statement, scope);
		} else if (statement instanceof LabeledStatementNode) {
			result = labeledStatement(function, lastStatement,
					(LabeledStatementNode) statement, scope);
		} else if (statement instanceof ReturnNode) {
			result = returnStatement(function, lastStatement,
					(ReturnNode) statement, scope);
		}
		function.addStatement(result);
		return result;
	}

	/**
	 * Takes a statement node where the start location and extra guard are
	 * defined elsewhere and returns the appropriate model statement.
	 * 
	 * @param location
	 *            The start location of the statement.
	 * @param guard
	 *            An extra component of the guard beyond that described in the
	 *            statement.
	 * @param function
	 *            The function containing this statement.
	 * @param lastStatement
	 *            The previous statement. Null if this is the first statement in
	 *            a function.
	 * @param statement
	 *            The statement node.
	 * @param scope
	 *            The scope containing this statement.
	 * @return The model representation of this statement.
	 */
	private Statement statement(Location location, Expression guard,
			Function function, Statement lastStatement,
			StatementNode statement, Scope scope) {
		Statement result = null;

		if (statement instanceof AssumeNode) {
			result = assume(function, lastStatement, (AssumeNode) statement,
					scope);
		} else if (statement instanceof AssertNode) {
			result = assertStatement(function, lastStatement,
					(AssertNode) statement, scope);
		} else if (statement instanceof ExpressionStatementNode) {
			result = expressionStatement(location, guard, function,
					lastStatement, (ExpressionStatementNode) statement, scope);
		} else if (statement instanceof CompoundStatementNode) {
			result = compoundStatement(location, guard, function,
					lastStatement, (CompoundStatementNode) statement, scope);
		} else if (statement instanceof ForLoopNode) {
			result = forLoop(function, lastStatement, (ForLoopNode) statement,
					scope);
		} else if (statement instanceof IfNode) {
			result = ifStatement(location, function, lastStatement,
					(IfNode) statement, scope);
		} else if (statement instanceof WaitNode) {
			result = wait(function, lastStatement, (WaitNode) statement, scope);
		} else if (statement instanceof NullStatementNode) {
			result = noop(location, function, lastStatement,
					(NullStatementNode) statement, scope);
		} else if (statement instanceof WhenNode) {
			result = when(location, guard, function, lastStatement,
					(WhenNode) statement, scope);
		} else if (statement instanceof ChooseStatementNode) {
			result = choose(function, lastStatement,
					(ChooseStatementNode) statement, scope);
		} else if (statement instanceof GotoNode) {
			result = gotoStatement(function, lastStatement,
					(GotoNode) statement, scope);
		} else if (statement instanceof LabeledStatementNode) {
			result = labeledStatement(location, guard, function, lastStatement,
					(LabeledStatementNode) statement, scope);
		} else if (statement instanceof ReturnNode) {
			result = returnStatement(function, lastStatement,
					(ReturnNode) statement, scope);
		}
		function.addStatement(result);
		return result;
	}

	/**
	 * An if statement.
	 */
	private Statement ifStatement(Function function, Statement lastStatement,
			IfNode statement, Scope scope) {
		return ifStatement(factory.location(scope), function, lastStatement,
				statement, scope);

	}

	private Statement ifStatement(Location location, Function function,
			Statement lastStatement, IfNode statement, Scope scope) {
		Expression expression = expression(statement.getCondition(), scope);
		Statement trueBranch = statement(location, expression, function,
				lastStatement, statement.getTrueBranch(), scope);
		Statement falseBranch;
		Location exitLocation = factory.location(scope);

		function.addLocation(location);
		if (lastStatement != null) {
			lastStatement.setTarget(location);
		} else {
			function.setStartLocation(location);
		}
		if (statement.getFalseBranch() == null) {
			falseBranch = factory.noopStatement(location);
			falseBranch.setGuard(factory.unaryExpression(UNARY_OPERATOR.NOT,
					expression));
		} else {
			falseBranch = statement(location,
					factory.unaryExpression(UNARY_OPERATOR.NOT, expression),
					function, lastStatement, statement.getFalseBranch(), scope);
		}
		function.addLocation(exitLocation);
		trueBranch.setTarget(exitLocation);
		falseBranch.setTarget(exitLocation);
		return factory.noopStatement(exitLocation);
	}

	/**
	 * An assume statement.
	 * 
	 * @param function
	 *            The function containing this statement.
	 * @param lastStatement
	 *            The previous statement. Null if this is the first statement in
	 *            a function.
	 * @param statement
	 *            The statement node.
	 * @param scope
	 *            The scope containing this statement.
	 * @return The model representation of this statement.
	 */
	private Statement assume(Function function, Statement lastStatement,
			AssumeNode statement, Scope scope) {
		Statement result;
		Expression expression = expression(statement.getExpression(), scope);
		Location location = factory.location(scope);

		result = factory.assumeStatement(location, expression);
		if (lastStatement != null) {
			lastStatement.setTarget(location);
		} else {
			function.setStartLocation(location);
		}
		return result;
	}

	/**
	 * An assert statement.
	 * 
	 * @param function
	 *            The function containing this statement.
	 * @param lastStatement
	 *            The previous statement. Null if this is the first statement in
	 *            a function.
	 * @param statement
	 *            The statement node.
	 * @param scope
	 *            The scope containing this statement.
	 * @return The model representation of this statement.
	 */
	private Statement assertStatement(Function function,
			Statement lastStatement, AssertNode statement, Scope scope) {
		Statement result;
		Expression expression = expression(statement.getExpression(), scope);
		Location location = factory.location(scope);

		function.addLocation(location);
		result = factory.assertStatement(location, expression);
		if (lastStatement != null) {
			lastStatement.setTarget(location);
		} else {
			function.setStartLocation(location);
		}
		return result;
	}

	/**
	 * Takes an expression statement and converts it to a model representation
	 * of that statement. Currently supported expressions for expression
	 * statements are spawn, assign, function call, increment, decrement. Any
	 * other expressions have no side effects and thus result in a no-op.
	 * 
	 * @param function
	 *            The function containing this statement.
	 * @param lastStatement
	 *            The previous statement. Null if this is the first statement in
	 *            a function.
	 * @param statement
	 *            The statement node.
	 * @param scope
	 *            The scope containing this statement.
	 * @return The model representation of this statement.
	 */
	private Statement expressionStatement(Function function,
			Statement lastStatement, ExpressionStatementNode statement,
			Scope scope) {
		Location location = factory.location(scope);
		Expression guard = factory.booleanLiteralExpression(true);

		function.addLocation(location);
		return expressionStatement(location, guard, function, lastStatement,
				statement, scope);
	}

	/**
	 * Takes an expression statement and converts it to a model representation
	 * of that statement. Currently supported expressions for expression
	 * statements are spawn, assign, function call, increment, decrement. Any
	 * other expressions have no side effects and thus result in a no-op.
	 * 
	 * @param location
	 *            The start location for this statement.
	 * @param guard
	 *            An extra guard associated with this statement.
	 * @param function
	 *            The function containing this statement.
	 * @param lastStatement
	 *            The previous statement. Null if this is the first statement in
	 *            a function.
	 * @param statement
	 *            The statement node.
	 * @param scope
	 *            The scope containing this statement.
	 * @return The model representation of this statement.
	 */
	private Statement expressionStatement(Location location, Expression guard,
			Function function, Statement lastStatement,
			ExpressionStatementNode statement, Scope scope) {
		Statement result = null;

		result = expressionStatement(location, guard, function,
				statement.getExpression(), scope);
		if (lastStatement != null) {
			lastStatement.setTarget(location);
		} else {
			function.setStartLocation(location);
		}
		if (result.guard().equals(factory.booleanLiteralExpression(true))) {
			result.setGuard(guard);
		} else if (!guard.equals(factory.booleanLiteralExpression(true))) {
			result.setGuard(factory.binaryExpression(BINARY_OPERATOR.AND,
					guard, result.guard()));
		}
		return result;
	}

	/**
	 * Create a statement from an expression.
	 * 
	 * @param location
	 * @param guard
	 * @param function
	 * @param lastStatement
	 * @param expression
	 * @param scope
	 */
	private Statement expressionStatement(Location location, Expression guard,
			Function function, ExpressionNode expressionStatement, Scope scope) {
		Statement result = null;

		if (expressionStatement instanceof OperatorNode) {
			OperatorNode expression = (OperatorNode) expressionStatement;
			switch (expression.getOperator()) {
			case ASSIGN:
				result = assign(location, expression.getArgument(0),
						expression.getArgument(1), scope);
				break;
			case POSTINCREMENT:
			case PREINCREMENT:
				Expression incrementVariable = expression(
						expression.getArgument(0), scope);

				result = factory
						.assignStatement(
								location,
								incrementVariable,
								factory.binaryExpression(
										BINARY_OPERATOR.PLUS,
										incrementVariable,
										factory.integerLiteralExpression(BigInteger.ONE)));
				break;
			case POSTDECREMENT:
			case PREDECREMENT:
				Expression decrementVariable = expression(
						expression.getArgument(0), scope);

				result = factory
						.assignStatement(
								location,
								decrementVariable,
								factory.binaryExpression(
										BINARY_OPERATOR.PLUS,
										decrementVariable,
										factory.integerLiteralExpression(BigInteger.ONE)));
				break;
			default:
				result = factory.noopStatement(location);
			}
		} else if (expressionStatement instanceof SpawnNode) {
			FunctionCallNode call = ((SpawnNode) expressionStatement).getCall();
			Expression name = factory
					.stringLiteralExpression(((IdentifierExpressionNode) call
							.getFunction()).getIdentifier().name());
			Vector<Expression> arguments = new Vector<Expression>();

			for (int i = 0; i < call.getNumberOfArguments(); i++) {
				arguments.add(expression(call.getArgument(i), scope));
			}
			result = factory.forkStatement(location, name, arguments);
		} else if (expressionStatement instanceof FunctionCallNode) {
			Vector<Expression> arguments = new Vector<Expression>();
			ExpressionNode functionExpression = ((FunctionCallNode) expressionStatement)
					.getFunction();
			FunctionDefinitionNode functionDefinition = null;
			String functionName = "";

			if (functionExpression instanceof IdentifierExpressionNode) {
				OrdinaryEntity functionEntity = functionExpression.getScope()
						.getLexicalOrdinaryEntity(
								((IdentifierExpressionNode) functionExpression)
										.getIdentifier().name());
				functionName = ((IdentifierExpressionNode) functionExpression)
						.getIdentifier().name();

				if (functionEntity instanceof edu.udel.cis.vsl.abc.ast.entity.IF.Function) {
					functionDefinition = ((edu.udel.cis.vsl.abc.ast.entity.IF.Function) functionEntity)
							.getDefinition();
				} else {
					// TODO: handle this.
				}
			} else {
				// TODO: handle this. Need to get the entity.
			}
			for (int i = 0; i < ((FunctionCallNode) expressionStatement)
					.getNumberOfArguments(); i++) {
				arguments
						.add(expression(
								((FunctionCallNode) expressionStatement)
										.getArgument(i), scope));
			}
			result = factory.callStatement(location, null, arguments);
			if (systemFunctions.containsKey(functionName)) {
				((CallStatement) result).setFunction(systemFunctions
						.get(functionName));
			} else {
				callStatements.put((CallStatement) result, functionDefinition);
			}
		}
		return result;
	}

	/**
	 * Sometimes an assignment is actually modeled as a fork or function call
	 * with an optional left hand side argument. Catch these cases.
	 * 
	 * @param location
	 *            The start location for this assign.
	 * @param lhs
	 *            AST expression for the left hand side of the assignment.
	 * @param rhs
	 *            AST expression for the right hand side of the assignment.
	 * @param scope
	 *            The scope containing this assignment.
	 * @return The model representation of the assignment, which might also be a
	 *         fork statement or function call.
	 */
	private Statement assign(Location location, ExpressionNode lhs,
			ExpressionNode rhs, Scope scope) {
		Expression lhsExpression = expression(lhs, scope);

		return assign(location, lhsExpression, rhs, scope);
	}

	/**
	 * Sometimes an assignment is actually modeled as a fork or function call
	 * with an optional left hand side argument. Catch these cases.
	 * 
	 * @param location
	 *            The start location for this assign.
	 * @param lhs
	 *            Model expression for the left hand side of the assignment.
	 * @param rhs
	 *            AST expression for the right hand side of the assignment.
	 * @param scope
	 *            The scope containing this assignment.
	 * @return The model representation of the assignment, which might also be a
	 *         fork statement or function call.
	 */
	private Statement assign(Location location, Expression lhs,
			ExpressionNode rhs, Scope scope) {
		Statement result = null;

		if (rhs instanceof FunctionCallNode) {
			FunctionDefinitionNode definition = findFunctionDefinition(((FunctionCallNode) rhs)
					.getFunction());
			Vector<Expression> arguments = new Vector<Expression>();

			for (int i = 0; i < ((FunctionCallNode) rhs).getNumberOfArguments(); i++) {
				arguments.add(expression(
						((FunctionCallNode) rhs).getArgument(i), scope));
			}
			result = factory.callStatement(location, null, arguments);
			((CallStatement) result).setLhs(lhs);
			if (systemFunctions.containsKey(definition.getName())) {
				((CallStatement) result).setFunction(systemFunctions
						.get(definition.getName()));
			} else {
				callStatements.put((CallStatement) result, definition);
			}
		} else if (rhs instanceof SpawnNode) {
			FunctionDefinitionNode definition = findFunctionDefinition(((SpawnNode) rhs)
					.getCall().getFunction());
			Vector<Expression> arguments = new Vector<Expression>();
			StringLiteralExpression functionName = factory
					.stringLiteralExpression(definition.getName());

			for (int i = 0; i < ((SpawnNode) rhs).getCall()
					.getNumberOfArguments(); i++) {
				arguments.add(expression(((SpawnNode) rhs).getCall()
						.getArgument(i), scope));
			}
			result = factory.forkStatement(location, lhs, functionName,
					arguments);
		} else {
			result = factory.assignStatement(location, lhs,
					expression(rhs, scope));
		}
		return result;
	}

	private FunctionDefinitionNode findFunctionDefinition(
			ExpressionNode function) {
		FunctionDefinitionNode result = null;

		if (function instanceof IdentifierExpressionNode) {
			Entity functionEntity = function.getScope()
					.getLexicalOrdinaryEntity(
							((IdentifierExpressionNode) function)
									.getIdentifier().name());

			assert functionEntity != null;
			assert functionEntity instanceof edu.udel.cis.vsl.abc.ast.entity.IF.Function;
			result = ((edu.udel.cis.vsl.abc.ast.entity.IF.Function) functionEntity)
					.getDefinition();
		} else {
			// TODO: Figure out more complicated function references.
		}
		return result;
	}

	private Statement compoundStatement(Function function,
			Statement lastStatement, CompoundStatementNode statement,
			Scope scope) {
		return compoundStatement(null, null, function, lastStatement,
				statement, scope);

	}

	private Statement compoundStatement(Location location, Expression guard,
			Function function, Statement lastStatement,
			CompoundStatementNode statement, Scope scope) {
		Scope newScope = factory.scope(scope, new LinkedHashSet<Variable>(),
				function);
		boolean usedLocation = false;

		// TODO: Handle everything that can be in here.
		for (int i = 0; i < statement.numChildren(); i++) {
			BlockItemNode node = statement.getSequenceChild(i);

			if (node instanceof VariableDeclarationNode) {
				InitializerNode init = ((VariableDeclarationNode) node)
						.getInitializer();
				processVariableDeclaration(newScope,
						(VariableDeclarationNode) node);
				if (init != null) {
					// TODO: Handle compound initializers
					Statement newStatement;
					if (usedLocation || location == null) {
						location = factory.location(newScope);
						usedLocation = true;
					} else {
						usedLocation = true;
					}
					newStatement = assign(location,
							factory.variableExpression(newScope
									.getVariable(newScope.numVariables() - 1)),
							(ExpressionNode) init, newScope);

					if (lastStatement != null) {
						lastStatement.setTarget(location);
						function.addLocation(location);
					} else {
						function.setStartLocation(location);
					}
					lastStatement = newStatement;
				}
			} else if (node instanceof FunctionDeclarationNode) {
				unprocessedFunctions.add((FunctionDefinitionNode) node);
				containingScopes.put((FunctionDefinitionNode) node, newScope);
			} else if (node instanceof StatementNode) {
				Statement newStatement;

				if (usedLocation || location == null) {
					usedLocation = true;
					newStatement = statement(function, lastStatement,
							(StatementNode) node, newScope);
				} else {
					usedLocation = true;
					newStatement = statement(location, guard, function,
							lastStatement, (StatementNode) node, newScope);
				}
				lastStatement = newStatement;
			} else {
				throw new RuntimeException("Unsupported block element: " + node);
			}
		}
		if (lastStatement == null) {
			if (location == null) {
				location = factory.location(newScope);
			}
			lastStatement = factory.noopStatement(location);
			function.setStartLocation(location);
		}
		return lastStatement;
	}

	private Statement forLoop(Function function, Statement lastStatement,
			ForLoopNode statement, Scope scope) {
		ForLoopInitializerNode init = statement.getInitializer();
		Statement initStatement = lastStatement;
		Scope newScope = factory.scope(scope, new LinkedHashSet<Variable>(),
				function);
		Statement loopBody;
		Expression condition;
		Statement incrementer;
		Statement loopExit;

		if (init != null) {
			if (init instanceof ExpressionNode) {
				Location initLocation = factory.location(newScope);

				initStatement = expressionStatement(initLocation,
						factory.booleanLiteralExpression(true), function,
						(ExpressionNode) init, scope);
				if (lastStatement != null) {
					lastStatement.setTarget(initLocation);
					function.addLocation(initLocation);
				} else {
					lastStatement = initStatement;
					function.setStartLocation(initLocation);
				}
			} else if (init instanceof DeclarationListNode) {
				for (int i = 0; i < ((DeclarationListNode) init).numChildren(); i++) {
					VariableDeclarationNode declaration = ((DeclarationListNode) init)
							.getSequenceChild(i);
					// TODO: Double check this is a variable
					processVariableDeclaration(newScope, declaration);
					if (declaration.getInitializer() != null) {
						Location initLocation = factory.location(newScope);

						initStatement = factory
								.assignStatement(
										initLocation,
										factory.variableExpression(newScope
												.getVariable(newScope
														.numVariables() - 1)),
										expression((ExpressionNode) declaration
												.getInitializer(), newScope));
						if (lastStatement != null) {
							lastStatement.setTarget(initLocation);
							function.addLocation(initLocation);
						} else {
							lastStatement = initStatement;
							function.setStartLocation(initLocation);
						}
					}
				}
			} else {
				throw new RuntimeException(
						"A for loop initializer must be an expression or a declaration list. "
								+ init);
			}
		}
		condition = expression(statement.getCondition(), newScope);
		loopBody = statement(function, initStatement, statement.getBody(),
				newScope);
		for (Statement outgoing : initStatement.target().outgoing()) {
			outgoing.setGuard(factory.binaryExpression(BINARY_OPERATOR.AND,
					outgoing.guard(), condition));
		}
		incrementer = forLoopIncrementer(function, loopBody,
				statement.getIncrementer(), newScope);
		incrementer.setTarget(initStatement.target());
		loopExit = factory.noopStatement(initStatement.target());
		loopExit.setGuard(factory
				.unaryExpression(UNARY_OPERATOR.NOT, condition));
		return loopExit;
	}

	private Statement forLoopIncrementer(Function function,
			Statement lastStatement, ExpressionNode incrementer, Scope scope) {
		Location location = factory.location(scope);
		Statement result;

		function.addLocation(location);
		// TODO: Handle other possibilites
		if (incrementer instanceof OperatorNode) {
			OperatorNode expression = (OperatorNode) incrementer;
			switch (expression.getOperator()) {
			case ASSIGN:
				result = factory.assignStatement(location,
						expression(expression.getArgument(0), scope),
						expression(expression.getArgument(1), scope));
				break;
			case POSTINCREMENT:
			case PREINCREMENT:
				Expression incrementVariable = expression(
						expression.getArgument(0), scope);

				result = factory
						.assignStatement(
								location,
								incrementVariable,
								factory.binaryExpression(
										BINARY_OPERATOR.PLUS,
										incrementVariable,
										factory.integerLiteralExpression(BigInteger.ONE)));
				break;
			case POSTDECREMENT:
			case PREDECREMENT:
				Expression decrementVariable = expression(
						expression.getArgument(0), scope);

				result = factory
						.assignStatement(
								location,
								decrementVariable,
								factory.binaryExpression(
										BINARY_OPERATOR.PLUS,
										decrementVariable,
										factory.integerLiteralExpression(BigInteger.ONE)));
				break;
			case PLUSEQ:
				Expression lhs = expression(expression.getArgument(0), scope);
				Expression rhs = expression(expression.getArgument(1), scope);

				result = factory.assignStatement(location, lhs, factory
						.binaryExpression(BINARY_OPERATOR.PLUS, lhs, rhs));
				break;
			// TODO: -=,*=,/=,%=
			default:
				result = factory.noopStatement(location);
			}
		} else {
			result = factory.noopStatement(location);
		}
		if (lastStatement != null) {
			lastStatement.setTarget(location);
		} else {
			function.setStartLocation(location);
		}
		return result;
	}

	private Statement wait(Function function, Statement lastStatement,
			WaitNode statement, Scope scope) {
		Location location = factory.location(scope);

		if (lastStatement != null) {
			lastStatement.setTarget(location);
		} else {
			function.setStartLocation(location);
		}
		function.addLocation(location);
		return factory.joinStatement(location,
				expression(statement.getExpression(), scope));
	}

	private Statement noop(Function function, Statement lastStatement,
			NullStatementNode statement, Scope scope) {
		Location location = factory.location(scope);

		return noop(location, function, lastStatement, statement, scope);
	}

	private Statement noop(Location location, Function function,
			Statement lastStatement, NullStatementNode statement, Scope scope) {
		Statement result = factory.noopStatement(location);

		function.addLocation(location);
		if (lastStatement != null) {
			lastStatement.setTarget(location);
		} else {
			function.setStartLocation(location);
		}
		return result;
	}

	private Statement when(Function function, Statement lastStatement,
			WhenNode statement, Scope scope) {
		Statement result = statement(function, lastStatement,
				statement.getBody(), scope);
		Expression guard = expression(statement.getGuard(), scope);
		Iterator<Statement> iter;

		// A $true or $false guard is translated as 1 or 0, but this causes
		// trouble later.
		if (guard instanceof IntegerLiteralExpression) {
			if (((IntegerLiteralExpression) guard).value().intValue() == 0) {
				guard = factory.booleanLiteralExpression(false);
			} else {
				guard = factory.booleanLiteralExpression(true);
			}
		}
		if (lastStatement != null) {
			iter = lastStatement.target().outgoing().iterator();
		} else {
			iter = function.startLocation().outgoing().iterator();
		}
		while (iter.hasNext()) {
			Statement s = iter.next();

			if (s.guard().equals(factory.booleanLiteralExpression(true))) {
				s.setGuard(guard);
			} else if (guard.equals(factory.booleanLiteralExpression(true))) {
				s.setGuard(guard);
			} else {
				s.setGuard(factory.binaryExpression(BINARY_OPERATOR.AND,
						s.guard(), guard));
			}
		}
		result.setGuard(guard);
		return result;
	}

	private Statement when(Location location, Expression guard,
			Function function, Statement lastStatement, WhenNode statement,
			Scope scope) {
		Expression newGuard = expression(statement.getGuard(), scope);
		Statement result;

		if (newGuard.equals(factory.booleanLiteralExpression(true))) {
			newGuard = guard;
		} else if (!guard.equals(factory.booleanLiteralExpression(true))) {
			newGuard = factory.binaryExpression(BINARY_OPERATOR.AND, guard,
					newGuard);
		}
		result = statement(location, newGuard, function, lastStatement,
				statement.getBody(), scope);
		return result;
	}

	private Statement choose(Function function, Statement lastStatement,
			ChooseStatementNode statement, Scope scope) {
		Location startLocation = factory.location(scope);
		Location endLocation = factory.location(scope);
		Statement result = factory.noopStatement(endLocation);
		Expression guard = factory.booleanLiteralExpression(true);
		int defaultOffset = 0;

		if (lastStatement != null) {
			lastStatement.setTarget(startLocation);
		} else {
			function.setStartLocation(startLocation);
		}
		function.addLocation(startLocation);
		if (statement.getDefaultCase() != null) {
			defaultOffset = 1;
		}
		for (int i = 0; i < statement.numChildren() - defaultOffset; i++) {
			Statement caseStatement = statement(startLocation,
					factory.booleanLiteralExpression(true), function,
					lastStatement, statement.getSequenceChild(i), scope);

			caseStatement.setTarget(endLocation);
		}
		Iterator<Statement> iter = startLocation.outgoing().iterator();
		// Compute the guard for the default statement
		while (iter.hasNext()) {
			Expression statementGuard = iter.next().guard();

			if (guard.equals(factory.booleanLiteralExpression(true))) {
				guard = statementGuard;
			} else if (statementGuard.equals(factory
					.booleanLiteralExpression(true))) {
				// Keep current guard
			} else {
				guard = factory.binaryExpression(BINARY_OPERATOR.OR, guard,
						statementGuard);
			}
		}
		if (statement.getDefaultCase() != null) {
			Statement defaultStatement = statement(startLocation,
					factory.unaryExpression(UNARY_OPERATOR.NOT, guard),
					function, lastStatement, statement.getDefaultCase(), scope);

			defaultStatement.setTarget(endLocation);
		}
		return result;
	}

	private Statement gotoStatement(Function function, Statement lastStatement,
			GotoNode statement, Scope scope) {
		Location location = factory.location(scope);
		Statement noop = factory.noopStatement(location);
		OrdinaryLabelNode label = ((Label) statement.getLabel().getEntity())
				.getDefinition();

		function.addLocation(location);
		if (lastStatement != null) {
			lastStatement.setTarget(location);
		} else {
			function.setStartLocation(location);
		}
		gotoStatements.put(noop, label);
		return noop;
	}

	private Statement labeledStatement(Function function,
			Statement lastStatement, LabeledStatementNode statement, Scope scope) {
		Statement result = statement(function, lastStatement,
				statement.getStatement(), scope);

		if (lastStatement != null) {
			labeledLocations.put(statement.getLabel(), lastStatement.target());
		} else {
			labeledLocations
					.put(statement.getLabel(), function.startLocation());
		}
		return result;
	}

	private Statement labeledStatement(Location location, Expression guard,
			Function function, Statement lastStatement,
			LabeledStatementNode statement, Scope scope) {
		Statement result = statement(location, guard, function, lastStatement,
				statement.getStatement(), scope);

		if (lastStatement != null) {
			labeledLocations.put(statement.getLabel(), lastStatement.target());
		} else {
			labeledLocations
					.put(statement.getLabel(), function.startLocation());
		}
		return result;
	}

	private Statement returnStatement(Function function,
			Statement lastStatement, ReturnNode statement, Scope scope) {
		Statement result;
		Expression expression = null;
		Location location = factory.location(scope);

		function.addLocation(location);
		if (lastStatement != null) {
			lastStatement.setTarget(location);
		} else {
			function.setStartLocation(location);
		}
		if (statement.getExpression() != null) {
			expression = expression(statement.getExpression(), scope);
		}
		result = factory.returnStatement(location, expression);
		return result;
	}
}
