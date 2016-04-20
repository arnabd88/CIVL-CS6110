package edu.udel.cis.vsl.abc.analysis.entity;

import edu.udel.cis.vsl.abc.ast.IF.ASTException;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.conversion.IF.Conversion;
import edu.udel.cis.vsl.abc.ast.conversion.IF.ConversionFactory;
import edu.udel.cis.vsl.abc.ast.entity.IF.Entity;
import edu.udel.cis.vsl.abc.ast.entity.IF.Entity.EntityKind;
import edu.udel.cis.vsl.abc.ast.entity.IF.Function;
import edu.udel.cis.vsl.abc.ast.entity.IF.OrdinaryEntity;
import edu.udel.cis.vsl.abc.ast.entity.IF.ProgramEntity.LinkageKind;
import edu.udel.cis.vsl.abc.ast.entity.IF.Variable;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.AttributeKey;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.NodeFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.PairNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.CallEventNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPIContractExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPIContractExpressionNode.MPIContractExpressionKind;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MemorySetNode;
import edu.udel.cis.vsl.abc.ast.node.IF.compound.CompoundInitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.compound.DesignationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.DeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.InitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.AlignOfNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ArrowNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.CallsNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.CastNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.CharacterConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.CompoundLiteralNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ContractVerifyNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.DerivativeExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.DotNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.EnumerationConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode.ExpressionKind;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FloatingConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.GenericSelectionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.HereOrRootNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IntegerConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ProcnullNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.QuantifiedExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.RegularRangeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.RemoteExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ResultNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ScopeOfNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.SelfNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.SizeableNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.SizeofNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.SpawnNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.StatementExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.StringLiteralNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.WildcardNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.FunctionTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.ast.type.IF.ArithmeticType;
import edu.udel.cis.vsl.abc.ast.type.IF.ArrayType;
import edu.udel.cis.vsl.abc.ast.type.IF.AtomicType;
import edu.udel.cis.vsl.abc.ast.type.IF.DomainType;
import edu.udel.cis.vsl.abc.ast.type.IF.EnumerationType;
import edu.udel.cis.vsl.abc.ast.type.IF.Enumerator;
import edu.udel.cis.vsl.abc.ast.type.IF.Field;
import edu.udel.cis.vsl.abc.ast.type.IF.FunctionType;
import edu.udel.cis.vsl.abc.ast.type.IF.IntegerType;
import edu.udel.cis.vsl.abc.ast.type.IF.ObjectType;
import edu.udel.cis.vsl.abc.ast.type.IF.PointerType;
import edu.udel.cis.vsl.abc.ast.type.IF.QualifiedObjectType;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardSignedIntegerType.SignedIntKind;
import edu.udel.cis.vsl.abc.ast.type.IF.StructureOrUnionType;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.ast.type.IF.Type.TypeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.TypeFactory;
import edu.udel.cis.vsl.abc.ast.type.IF.UnqualifiedObjectType;
import edu.udel.cis.vsl.abc.config.IF.Configuration;
import edu.udel.cis.vsl.abc.config.IF.Configurations.Language;
import edu.udel.cis.vsl.abc.err.IF.ABCRuntimeException;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.token.IF.UnsourcedException;

/**
 * Analyzes expressions in an AST.
 * 
 * Scopes: can occur in the following situations:
 * 
 * <pre>
 * $scope s;       // declaration of concrete scope variable s
 * <s> f(...)      // introduction of scope variable s in function decl
 * <s> typedef ... // introduction of scope variable s in typedef decl
 * <s> struct ...  // introduction of scope variables s in struct decl
 * double *<s> p;  // use of scope expr s in pointer restriction
 * f<s>(...)       // use of scope expr s in function call instance
 * t<s> x;         // use of scope expr s in typedef instance
 * struct t<s> x;  // use of scope expr s in struct instance
 * 
 * </pre>
 * 
 * The scope expressions (i.e., expressions of scope type) are: ScopeVariables
 * and expressions of the form ScopeOf(lhs). Later expression may be added (like
 * join).
 * 
 * A ScopeValue can be either a (concrete) scope (an instance of Scope), or a
 * ScopeVariable (a parameter scope variable, not a concrete one). Later values
 * may be added (like join).
 * 
 * A scope expression can always be evaluated statically to a ScopeValue.
 * 
 * Need to process a scope expression and to evaluate a scope expression to get
 * the ScopeValue.
 * 
 * @author siegel
 * 
 */
public class ExpressionAnalyzer {

	// ***************************** Fields *******************************

	private EntityAnalyzer entityAnalyzer;

	private ConversionFactory conversionFactory;

	private TypeFactory typeFactory;

	private ASTFactory astFactory;

	private NodeFactory nodeFactory;

	/**
	 * needs the statement analyzer for analyzing statement expression (GNU C
	 * extension)
	 */
	private StatementAnalyzer statementAnalyzer;

	private IntegerType intType;

	private StandardBasicType boolType;

	private SpecialFunctionCallAnalyzer specialCallAnalyzer;

	private Configuration config;

	private Language language;

	private AttributeKey unknownIdentifier;

	// private List<IdentifierExpressionNode> unknownIdentifiers = new
	// LinkedList<>();

	// ************************** Constructors ****************************

	ExpressionAnalyzer(EntityAnalyzer entityAnalyzer,
			ConversionFactory conversionFactory, TypeFactory typeFactory) {
		this.entityAnalyzer = entityAnalyzer;
		this.conversionFactory = conversionFactory;
		this.typeFactory = typeFactory;
		this.intType = typeFactory.signedIntegerType(SignedIntKind.INT);
		this.boolType = typeFactory.basicType(BasicTypeKind.BOOL);
		this.astFactory = entityAnalyzer.astFactory;
		this.nodeFactory = astFactory.getNodeFactory();
		// this.language = entityAnalyzer.configuration.getLanguage();
		this.specialCallAnalyzer = new SpecialFunctionCallAnalyzer(
				this.entityAnalyzer, typeFactory, this.conversionFactory);
		this.config = entityAnalyzer.configuration;
		this.language = entityAnalyzer.language;
		unknownIdentifier = this.nodeFactory.newAttribute("unknown_identifier",
				Boolean.class);
	}

	void setStatementAnalyzer(StatementAnalyzer statementAnalyzer) {
		this.statementAnalyzer = statementAnalyzer;
	}

	// ************************* Exported Methods **************************

	/**
	 * Processes an expression node. This method will set the type of node and
	 * the converted type of all of node's children nodes.
	 * 
	 * @param node
	 *            an expression node
	 * @throws SyntaxException
	 */
	void processExpression(ExpressionNode node) throws SyntaxException {
		try {
			switch (node.expressionKind()) {
			case ALIGNOF:
				processAlignOf((AlignOfNode) node);
				break;
			case ARROW:
				processArrow((ArrowNode) node);
				break;
			case CAST:
				processCast((CastNode) node);
				break;
			case COMPOUND_LITERAL:
				processCompoundLiteral((CompoundLiteralNode) node);
				break;
			case CONSTANT:
				processConstant((ConstantNode) node);
				break;
			case CONTRACT_VERIFY:
				processContractVerify((ContractVerifyNode) node);
				break;
			case DERIVATIVE_EXPRESSION:
				processDerivativeExpression((DerivativeExpressionNode) node);
				break;
			case DOT:
				processDot((DotNode) node);
				break;
			case FUNCTION_CALL:
				processFunctionCall((FunctionCallNode) node);
				break;
			case GENERIC_SELECTION:
				processGenericSelection((GenericSelectionNode) node);
				break;
			case IDENTIFIER_EXPRESSION:
				processIdentifierExpression((IdentifierExpressionNode) node,
						true, false);
				break;
			case OPERATOR:
				processOperator((OperatorNode) node);
				break;
			case QUANTIFIED_EXPRESSION:
				processQuantifiedExpression((QuantifiedExpressionNode) node);
				break;
			case REGULAR_RANGE:
				processRegularRange((RegularRangeNode) node);
				break;
			case REMOTE_REFERENCE:
				processRemoteExpression((RemoteExpressionNode) node);
				break;
			case RESULT:
				processResult((ResultNode) node);
				break;
			case SCOPEOF:
				processScopeOf((ScopeOfNode) node);
				break;
			case SIZEOF:
				processSizeof((SizeofNode) node);
				break;
			case SPAWN:
				processSpawn((SpawnNode) node);
				break;
			case CALLS:
				processCalls((CallsNode) node);
				break;
			case STATEMENT_EXPRESSION:
				processStatementExpression((StatementExpressionNode) node);
				break;
			case MPI_CONTRACT_EXPRESSION:
				processMPIContractExpression((MPIContractExpressionNode) node);
				break;
			case MEMORY_SET:
				processMemorySet((MemorySetNode) node);
				break;
			case WILDCARD:
				node.setInitialType(typeFactory.voidType());
				break;
			case NOTHING:
				node.setInitialType(this.typeFactory.memoryType());
				break;
			default:
				throw new ABCRuntimeException("Unreachable");

			}
		} catch (ASTException e) {
			throw new SyntaxException(e.getMessage(), node.getSource());
		}
	}

	private void processMemorySet(MemorySetNode node) throws SyntaxException {
		ExpressionNode element = node.getElements();
		SequenceNode<VariableDeclarationNode> binders = node.getBinders();
		ExpressionNode predicate = node.getPredicate();
		Type elementType;

		if (binders != null)
			for (VariableDeclarationNode variable : binders)
				entityAnalyzer.declarationAnalyzer
						.processVariableDeclaration(variable);
		this.processExpression(element);
		if (predicate != null)
			this.processExpression(predicate);
		elementType = element.getConvertedType();
		if (elementType instanceof ArithmeticType) {
			if (((ArithmeticType) elementType).isInteger())
				node.setInitialType(this.typeFactory.rangeType());
		} else if (elementType instanceof PointerType) {
			node.setInitialType(this.typeFactory.memoryType());
		}
		if (node.getConvertedType() == null)
			throw this.error("set of " + elementType
					+ " type is not supported yet", node);
	}

	/**
	 * processes a statement expression
	 * 
	 * @param statementExpression
	 * @throws SyntaxException
	 */
	private void processStatementExpression(
			StatementExpressionNode statementExpression) throws SyntaxException {
		this.statementAnalyzer.processCompoundStatement(statementExpression
				.getCompoundStatement());
		statementExpression.setInitialType(statementExpression.getExpression()
				.getType());
	}

	/**
	 * Given the type of the left hand side of an assignment, and the expression
	 * which is the right hand side, this method will add any conversions needed
	 * to the right hand side and return the type of the assignment, i.e., the
	 * result of applying lvalue conversion to the left hand side type. This
	 * method may be used for initializations in variable declarations, as well
	 * as simple assignments.
	 * 
	 * @param lhsType
	 *            type of left hand side
	 * @param rhs
	 *            expression
	 * @return type of assignment
	 * @throws UnsourcedException
	 *             if the types are not compatible
	 * @throws SyntaxException
	 */
	UnqualifiedObjectType processAssignment(ObjectType lhsType,
			ExpressionNode rhs) throws UnsourcedException, SyntaxException {
		UnqualifiedObjectType type = conversionFactory
				.lvalueConversionType(lhsType);

		if (!typeFactory.isArrayOfCharType(lhsType))
			addStandardConversions(rhs);
		convertRHS(rhs, type);
		return type;
	}

	/**
	 * For any IdentifierExpressionNode representing a function that has the
	 * attribute unknownIdentifier set as true, this method tries to analyze it
	 * and get its entity.
	 * 
	 * @param node
	 * @throws SyntaxException
	 */
	void processUnknownIdentifiers(ASTNode node) throws SyntaxException {
		if (node instanceof IdentifierExpressionNode) {
			Object unknownIdentiferAttribute = node
					.getAttribute(unknownIdentifier);

			if (unknownIdentiferAttribute != null
					&& (boolean) unknownIdentiferAttribute)
				this.processIdentifierExpression(
						(IdentifierExpressionNode) node, false, false);
		} else if (node instanceof WildcardNode) {
			WildcardNode wildcard = (WildcardNode) node;

			if (typeFactory.isVoidType(wildcard.getConvertedType())) {
				ASTNode callEventNode0 = wildcard.parent().parent();

				if (callEventNode0 instanceof CallEventNode) {
					CallEventNode callEventNode = (CallEventNode) callEventNode0;
					Function function = (Function) callEventNode.getFunction()
							.getIdentifier().getEntity();
					FunctionType functionType = function.getType();

					wildcard.setInitialType(functionType
							.getParameterType(wildcard.childIndex()));
				}
			}
		} else {
			for (ASTNode child : node.children()) {
				if (child != null)
					processUnknownIdentifiers(child);
			}
		}
	}

	/**
	 * <p>
	 * Processes a compound initializer node for which the type is a domain
	 * type.
	 * </p>
	 * 
	 * <p>
	 * The following are checked: (1) if the domain type is domain(n), then the
	 * length of the initializer list is n; (2) each of the pairs in the
	 * initializer list will have a null designation; (3) each of the pairs in
	 * the initializer list will have a non-null initializer which is an
	 * expression of range type. If any of the checks fail, a syntax exception
	 * is thrown.
	 * </p>
	 * 
	 * <p>
	 * Assuming all the checks pass, the following will be completed: each of
	 * the range expressions will be processed; the type of this compound
	 * initializer node will be set to the specific domain type, domain(n) (even
	 * if the given type was just the universal domain type <code>$domain</code>
	 * , without specifying n).
	 * </p>
	 * 
	 * @param type
	 *            the expected type of this compound initializer; must be a
	 *            domain type
	 * @param node
	 *            a compound literal node with domain type
	 * 
	 * @throws SyntaxException
	 *             if any of the above properties is violated, or there is a
	 *             syntax exception generated when checking the range
	 *             expressions
	 */
	void processCartesianDomainInitializer(CompoundInitializerNode initNode,
			DomainType type) throws SyntaxException {
		int numRanges = initNode.numChildren();

		if (type.hasDimension()) {
			int dimension = type.getDimension();

			if (dimension != numRanges)
				throw error("Expected " + dimension
						+ " ranges in Cartesian domain initializer, but saw "
						+ numRanges, initNode);
		}
		for (int i = 0; i < numRanges; i++) {
			PairNode<DesignationNode, InitializerNode> pair = initNode
					.getSequenceChild(i);
			InitializerNode rangeNode = pair.getRight();
			ExpressionNode rangeExpression;
			Type rangeNodeType;

			if (pair.getLeft() != null)
				throw error(
						"A designation may not be used in a Cartesian domain literal",
						pair.getLeft());
			if (rangeNode == null)
				throw error("Missing range expression at position " + i
						+ " in Cartesian domain literal", initNode);
			if (!(rangeNode instanceof ExpressionNode))
				throw error("Expected an expression", rangeNode);
			rangeExpression = (ExpressionNode) rangeNode;
			processExpression(rangeExpression);
			rangeNodeType = rangeExpression.getConvertedType();
			if (rangeNodeType.kind() != TypeKind.RANGE)
				throw error(
						"Expected expression of range type in Cartesian domain literal",
						rangeExpression);
		}
		if (!type.hasDimension())
			type = typeFactory.domainType(numRanges);
		initNode.setType(type);
	}

	// ************************ Private Methods ***************************

	private void processAlignOf(AlignOfNode node) throws SyntaxException {
		entityAnalyzer.typeAnalyzer.processTypeNode(node.getArgument());
		node.setInitialType(typeFactory.size_t());
	}

	/**
	 * C11 Sec. 6.5.2.3:
	 * 
	 * "The first operand of the -> operator shall have type "pointer to atomic,
	 * qualified, or unqualified structure" or "pointer to atomic, qualified, or
	 * unqualified union", and the second operand shall name a member of the
	 * type pointed to."
	 * 
	 * "A postfix expression followed by the -> operator and an identifier
	 * designates a member of a structure or union object. The value is that of
	 * the named member of the object to which the first expression points, and
	 * is an lvalue. If the first expression is a pointer to a qualified type,
	 * the result has the so-qualified version of the type of the designated
	 * member."
	 * 
	 * "Accessing a member of an atomic structure or union object results in
	 * undefined behavior."
	 * 
	 * @param node
	 * @throws SyntaxException
	 */
	private void processArrow(ArrowNode node) throws SyntaxException {
		IdentifierNode identifier = node.getFieldName();
		ExpressionNode pointerNode = node.getStructurePointer();
		String fieldName = identifier.name();
		StructureOrUnionType structureOrUnionType;
		boolean atomicQ = false, restrictQ = false, constQ = false, volatileQ = false;
		Field field;
		Type tempType, type;
		ObjectType fieldType;

		processExpression(pointerNode);
		addLvalueConversion(pointerNode);
		tempType = pointerNode.getConvertedType();
		if (tempType.kind() != TypeKind.POINTER)
			throw error("Left operand of arrow operator not pointer",
					pointerNode);
		tempType = ((PointerType) tempType).referencedType();
		if (tempType.kind() == TypeKind.QUALIFIED) {
			QualifiedObjectType qType = (QualifiedObjectType) tempType;

			constQ = qType.isConstQualified();
			restrictQ = qType.isRestrictQualified();
			volatileQ = qType.isVolatileQualified();
			tempType = qType.getBaseType();
		}
		if (tempType.kind() == TypeKind.ATOMIC) {
			atomicQ = true;
			tempType = ((AtomicType) tempType).getBaseType();
		}
		if (tempType.kind() != TypeKind.STRUCTURE_OR_UNION)
			throw error(
					"Left operand of arrow operator not pointer to structure or union",
					pointerNode);
		structureOrUnionType = (StructureOrUnionType) tempType;
		if (!structureOrUnionType.isComplete())
			throw error(
					"Structure or union type " + structureOrUnionType.getTag()
							+ " is incomplete", node);
		field = structureOrUnionType.getField(fieldName);
		if (field == null)
			throw error(
					"Structure or union type " + structureOrUnionType.getTag()
							+ " contains no field named " + fieldName,
					identifier);
		identifier.setEntity(field);
		fieldType = field.getType();
		type = typeFactory.qualify(fieldType, atomicQ, constQ, volatileQ,
				restrictQ, false, false);
		node.setInitialType(type);
	}

	private void processCast(CastNode node) throws SyntaxException {
		TypeNode typeNode = node.getCastType();
		ExpressionNode expression = node.getArgument();

		entityAnalyzer.typeAnalyzer.processTypeNode(typeNode);
		processExpression(expression);
		addStandardConversions(expression);
		node.setInitialType(typeNode.getType());
	}

	private void processCompoundLiteral(CompoundLiteralNode node)
			throws SyntaxException {
		Type type = entityAnalyzer.typeAnalyzer.processTypeNode(node
				.getTypeNode());
		CompoundInitializerNode initNode = node.getInitializerList();

		if (!(type instanceof ObjectType))
			throw error("Compound literal has non-object type: " + type, node);
		if (type.kind() == TypeKind.DOMAIN)
			processCartesianDomainInitializer(initNode, (DomainType) type);
		else
			entityAnalyzer.compoundLiteralAnalyzer.processCompoundInitializer(
					initNode, (ObjectType) type);
		node.setInitialType(initNode.getType());
	}

	private void processConstant(ConstantNode node) throws SyntaxException {
		if (node instanceof CharacterConstantNode) {
			// type should already be set
		} else if (node instanceof IntegerConstantNode) {
			// type should already be set.
		} else if (node instanceof EnumerationConstantNode) {
			String name = node.getStringRepresentation();
			OrdinaryEntity entity = node.getScope().getLexicalOrdinaryEntity(
					false, name);
			EntityKind kind;
			EnumerationType type;

			if (entity == null)
				throw error("Undeclared enumeration constant?", node);
			kind = entity.getEntityKind();
			if (kind != EntityKind.ENUMERATOR)
				throw error("Use of " + kind + " " + name
						+ " as enumeration constant?", node);
			type = ((Enumerator) entity).getType();
			node.setInitialType(type);
			((EnumerationConstantNode) node).getName().setEntity(entity);
			nodeFactory
					.setConstantValue(node, ((Enumerator) entity).getValue());
		} else if (node instanceof FloatingConstantNode) {
			// type should already be set
		} else if (node instanceof StringLiteralNode) {
			// type should already be set
		} else if (node instanceof SelfNode) {
			// type is process type, already set
		} else if (node instanceof ProcnullNode) {
			// type is process type, already set
		} else if (node instanceof HereOrRootNode) {
			// type is scope type, already set
		}
		// else
		// throw new RuntimeException("Unknown kind of constant node: " + node);
		if (node.getInitialType() == null)
			throw error("Internal error: did not set type", node);
	}

	/**
	 * C11 Sec. 6.5.2.3:
	 * 
	 * "The first operand of the . operator shall have an atomic, qualified, or
	 * unqualified structure or union type, and the second operand shall name a
	 * member of that type."
	 * 
	 * "A postfix expression followed by the . operator and an identifier
	 * designates a member of a structure or union object. The value is that of
	 * the named member, and is an lvalue if the first expression is an lvalue.
	 * If the first expression has qualified type, the result has the
	 * so-qualified version of the type of the designated member."
	 * 
	 * @param node
	 * @throws SyntaxException
	 */
	private void processDot(DotNode node) throws SyntaxException {
		ExpressionNode expression = node.getStructure();
		IdentifierNode identifier = node.getFieldName();
		String fieldName = identifier.name();
		boolean atomicQ = false, restrictQ = false, constQ = false, volatileQ = false;
		StructureOrUnionType structureOrUnionType;
		ObjectType fieldType;
		Type tempType, type;
		Field field;

		processExpression(expression);
		tempType = expression.getType();
		// no lvalue conversion for left operand of . operator:
		if (tempType.kind() == TypeKind.QUALIFIED) {
			QualifiedObjectType qType = (QualifiedObjectType) tempType;

			constQ = qType.isConstQualified();
			restrictQ = qType.isRestrictQualified();
			volatileQ = qType.isVolatileQualified();
			tempType = qType.getBaseType();
		}
		if (tempType.kind() == TypeKind.ATOMIC) {
			atomicQ = true;
			tempType = ((AtomicType) tempType).getBaseType();
		}
		if (tempType.kind() != TypeKind.STRUCTURE_OR_UNION)
			throw error("Left operand of dot operator not structure or union",
					expression);
		structureOrUnionType = (StructureOrUnionType) tempType;
		if (!structureOrUnionType.isComplete())
			throw error(
					"Structure or union type " + structureOrUnionType.getTag()
							+ " is incomplete", expression);
		field = structureOrUnionType.getField(fieldName);
		if (field == null)
			throw error(
					"Structure or union type " + structureOrUnionType.getTag()
							+ " contains no field named " + fieldName,
					identifier);
		identifier.setEntity(field);
		fieldType = field.getType();
		type = typeFactory.qualify(fieldType, atomicQ, constQ, volatileQ,
				restrictQ, false, false);
		node.setInitialType(type);
	}

	private void processScopeOf(ScopeOfNode node) throws SyntaxException {
		ExpressionNode expressionNode = node.expression();

		processExpression(expressionNode);
		node.setInitialType(typeFactory.scopeType());
	}

	private void processFunctionCall(FunctionCallNode node)
			throws SyntaxException {
		ExpressionNode functionNode = node.getFunction();
		int numArgs = node.getNumberOfArguments();
		int numContextArgs = node.getNumberOfContextArguments();
		FunctionType functionType;
		int expectedNumArgs = -1;
		boolean hasVariableNumArgs = false;
		boolean isSpecialFunction = false;
		String functionName = null;

		processExpression(functionNode);
		{
			Type tmpType = functionNode.getType();
			TypeKind tmpKind = tmpType == null ? TypeKind.FUNCTION : tmpType
					.kind();

			if (tmpKind == TypeKind.POINTER) {
				tmpType = ((PointerType) tmpType).referencedType();
				tmpKind = tmpType.kind();
			}
			if (tmpKind == TypeKind.FUNCTION)
				functionType = (FunctionType) tmpType;
			else
				throw error(
						"Function expression in function call does not have function "
								+ "type or pointer to function type",
						functionNode);
		}

		// TODO: Sanity checks on kernel functions
		// Check that context arg 0 is an int or dim3
		// Check that context arg 1 is an int or dim3
		// Check that context arg 2, if present, is a pointer to a stream
		// It might be appropriate to factor out these Cuda-specific checks into
		// a separate function

		if (functionNode instanceof IdentifierExpressionNode) {
			functionName = ((IdentifierExpressionNode) functionNode)
					.getIdentifier().name();
		}
		if (functionName != null)
			specialCallAnalyzer.hasSufficientArgumentsForPrintf(node,
					functionName, node.getArguments());
		if (functionType != null) {
			expectedNumArgs = functionType.getNumParameters();
			hasVariableNumArgs = functionType.hasVariableArgs();
			if (hasVariableNumArgs) {
				// if function has variable number of args then the number of
				// actual parameters must be at least the number expected
				if (numArgs < expectedNumArgs)
					throw error("Expected at least " + expectedNumArgs
							+ " arguments, saw " + numArgs, node);
				isSpecialFunction = this.specialCallAnalyzer
						.isSpecialFunction(functionName);
			} else {
				if (numArgs != expectedNumArgs)
					throw error("Expected " + expectedNumArgs
							+ " arguments but saw " + numArgs, node);
			}
		}
		for (int i = 0; i < numContextArgs; i++) {
			ExpressionNode argument = node.getContextArgument(i);

			processExpression(argument);
		}
		for (int i = 0; i < numArgs; i++) {
			ExpressionNode argument = node.getArgument(i);

			processExpression(argument);
			addStandardConversions(argument);
			specialCallAnalyzer.addConversionsForSpecialFunctions(functionName,
					argument);
			if ((functionType != null && (!hasVariableNumArgs || i < expectedNumArgs))
					|| isSpecialFunction) {
				ObjectType lhsType;
				UnqualifiedObjectType type;

				if (i < expectedNumArgs)
					lhsType = functionType.getParameterType(i);
				else
					lhsType = this.specialCallAnalyzer.variableParameterType(
							functionName, i);
				type = conversionFactory.lvalueConversionType(lhsType);
				try {
					convertRHS(argument, type);
				} catch (UnsourcedException e) {
					throw error(e, argument);
				}
			}
		}
		node.setInitialType(functionType == null ? this.typeFactory
				.basicType(BasicTypeKind.INT) : functionType.getReturnType());
	}

	private void processContractVerify(ContractVerifyNode node)
			throws SyntaxException {
		ExpressionNode functionNode = node.getFunction();
		int numArgs = node.getNumberOfArguments();
		int numContextArgs = node.getNumberOfContextArguments();
		FunctionType functionType;
		int expectedNumArgs = -1;
		boolean hasVariableNumArgs = false;
		boolean isSpecialFunction = false;
		String functionName = null;

		processExpression(functionNode);
		{
			Type tmpType = functionNode.getType();
			TypeKind tmpKind = tmpType == null ? TypeKind.FUNCTION : tmpType
					.kind();

			if (tmpKind == TypeKind.POINTER) {
				tmpType = ((PointerType) tmpType).referencedType();
				tmpKind = tmpType.kind();
			}
			if (tmpKind == TypeKind.FUNCTION)
				functionType = (FunctionType) tmpType;
			else
				throw error(
						"Function expression in contract verify call does not have function "
								+ "type or pointer to function type",
						functionNode);
		}

		// TODO: Sanity checks on kernel functions
		// Check that context arg 0 is an int or dim3
		// Check that context arg 1 is an int or dim3
		// Check that context arg 2, if present, is a pointer to a stream
		// It might be appropriate to factor out these Cuda-specific checks into
		// a separate function

		if (functionNode instanceof IdentifierExpressionNode) {
			functionName = ((IdentifierExpressionNode) functionNode)
					.getIdentifier().name();
		}
		if (functionName != null)
			specialCallAnalyzer.hasSufficientArgumentsForPrintf(node,
					functionName, node.getArguments());
		if (functionType != null) {
			expectedNumArgs = functionType.getNumParameters();
			hasVariableNumArgs = functionType.hasVariableArgs();
			if (hasVariableNumArgs) {
				// if function has variable number of args then the number of
				// actual parameters must be at least the number expected
				if (numArgs < expectedNumArgs)
					throw error("Expected at least " + expectedNumArgs
							+ " arguments, saw " + numArgs, node);
				isSpecialFunction = this.specialCallAnalyzer
						.isSpecialFunction(functionName);
			} else {
				if (numArgs != expectedNumArgs)
					throw error("Expected " + expectedNumArgs
							+ " arguments but saw " + numArgs, node);
			}
		}
		for (int i = 0; i < numContextArgs; i++) {
			ExpressionNode argument = node.getContextArgument(i);

			processExpression(argument);
		}
		for (int i = 0; i < numArgs; i++) {
			ExpressionNode argument = node.getArgument(i);

			processExpression(argument);
			addStandardConversions(argument);
			specialCallAnalyzer.addConversionsForSpecialFunctions(functionName,
					argument);
			if ((functionType != null && (!hasVariableNumArgs || i < expectedNumArgs))
					|| isSpecialFunction) {
				ObjectType lhsType;
				UnqualifiedObjectType type;

				if (i < expectedNumArgs)
					lhsType = functionType.getParameterType(i);
				else
					lhsType = this.specialCallAnalyzer.variableParameterType(
							functionName, i);
				type = conversionFactory.lvalueConversionType(lhsType);
				try {
					convertRHS(argument, type);
				} catch (UnsourcedException e) {
					throw error(e, argument);
				}
			}
		}
		node.setInitialType(functionType == null ? this.typeFactory
				.basicType(BasicTypeKind.INT) : functionType.getReturnType());
	}

	private void processSpawn(SpawnNode node) throws SyntaxException {
		processFunctionCall(node.getCall());
		node.setInitialType(typeFactory.processType());
	}

	private void processCalls(CallsNode node) throws SyntaxException {
		processFunctionCall(node.getCall());
		node.setInitialType(typeFactory.basicType(BasicTypeKind.BOOL));
	}

	private void processGenericSelection(GenericSelectionNode node)
			throws SyntaxException {
		// TODO
	}

	/**
	 * Apparently, special handling is required for functions which were
	 * declared only with identifier lists. in this case, the type of the
	 * identifier expression does not get the full type of the function, only
	 * the return type. See <a href=
	 * "http://stackoverflow.com/questions/24743887/are-these-compatible-function-types-in-c"
	 * >here</a>.
	 */
	private FunctionType getFunctionExpressionType(
			IdentifierExpressionNode node, Function function) {
		FunctionType functionType = function.getType();
		FunctionType result = null;

		if (node.parent() instanceof FunctionCallNode) {
			result = functionType;
		} else {
			for (DeclarationNode dn : function.getDeclarations()) {
				FunctionDeclarationNode decl = (FunctionDeclarationNode) dn;
				FunctionTypeNode typeNode = decl.getTypeNode();

				if (!typeNode.hasIdentifierList()) {
					result = functionType;
					break;
				}
			}
			if (result == null)
				// if you've made it to this point, all declarations of the
				// function
				// have identifier lists; none has a parameter-type list
				result = typeFactory.functionType(functionType.getReturnType());
		}
		return result;
	}

	void processIdentifierExpression(IdentifierExpressionNode node,
			boolean isFirstRound, boolean isContract) throws SyntaxException {
		IdentifierNode identifierNode = node.getIdentifier();
		String name = identifierNode.name();
		OrdinaryEntity entity = node.getScope().getLexicalOrdinaryEntity(false,
				name);
		EntityKind kind;

		if (entity == null) {
			if (isFirstRound && (config.svcomp() || isContract)) {
				node.setAttribute(unknownIdentifier, true);
				return;
			} else {
				throw error("Undeclared identifier " + name, node);
			}
		}
		kind = entity.getEntityKind();
		switch (kind) {
		case VARIABLE:
			if (isFirstRound)
				node.setInitialType(entity.getType());
			else
				throw error("Undeclared identifier " + name, node);
			break;
		case FUNCTION:
			node.setInitialType(getFunctionExpressionType(node,
					(Function) entity));
			break;
		default:
			throw error("Use of " + kind + " " + name + " as expression", node);
		}
		identifierNode.setEntity(entity);
		// only checks external definition for whole-program AST
		if (node.getOwner().isWholeProgram()) {
			this.checkExternalDefinitionOfIdentifier(node);
		}
	}

	/**
	 * When an identifier is used in an expression except for
	 * <code>sizeof</code> or <code>_Alignof</code>, if its declaration is a
	 * variable with external linkage, then report an error if the external
	 * definition is missing.
	 * 
	 * @param identifierExpression
	 *            the identifier expression node being checked
	 * @throws SyntaxException
	 */
	private void checkExternalDefinitionOfIdentifier(
			IdentifierExpressionNode identifierExpression)
			throws SyntaxException {
		ASTNode parent = identifierExpression.parent();

		if (parent instanceof ExpressionNode) {
			ExpressionNode expression = (ExpressionNode) parent;
			ExpressionKind kind = expression.expressionKind();

			if (kind != ExpressionKind.ALIGNOF && kind != ExpressionKind.SIZEOF) {
				Entity entity = identifierExpression.getIdentifier()
						.getEntity();

				if (entity.getEntityKind() == EntityKind.VARIABLE) {
					Variable variable = (Variable) entity;
					VariableDeclarationNode definition = variable
							.getDefinition();

					// don't check $input variables
					if (variable.getDeclaration(0).getTypeNode()
							.isInputQualified())
						return;

					// tentative definitions are OK
					boolean noStorage = true;

					for (DeclarationNode declaration : variable
							.getDeclarations()) {
						VariableDeclarationNode varDeclaration = (VariableDeclarationNode) declaration;

						if (varDeclaration.hasAutoStorage()
								|| varDeclaration.hasRegisterStorage()
								|| varDeclaration.hasThreadLocalStorage()
								|| varDeclaration.hasExternStorage()) {
							noStorage = false;
							break;
						}
					}
					if (noStorage)
						return;

					if (variable.getLinkage() == LinkageKind.EXTERNAL) {
						if (definition == null)
							throw this.error("the definition for the variable "
									+ variable.getName() + " which is declared"
									+ " with external linkage is missing",
									identifierExpression);
					}
				}
			}
		}
	}

	private void processOperator(OperatorNode node) throws SyntaxException {
		Operator operator = node.getOperator();
		int numArgs = node.getNumberOfArguments();

		// the following sets the initial type of each argument:
		for (int i = 0; i < numArgs; i++) {
			ExpressionNode child = node.getArgument(i);

			if (child == null)
				throw new ASTException("Child " + i
						+ " of operator node is null:\n" + node);
			processExpression(child);
		}
		switch (operator) {
		case ADDRESSOF: // & pointer to object
			processADDRESSOF(node);
			break;
		case ASSIGN: // = standard assignment operator
			processASSIGN(node);
			break;
		case HASH:
			processHash(node);
			break;
		case BIG_O: // big-O expresion
			processBIG_O(node);
			break;
		case BITAND: // & bit-wise and
		case BITOR: // | bit-wise inclusive or
		case BITXOR: // ^ bit-wise exclusive or
			processBitwise(node);
			break;
		case BITANDEQ: // &= bit-wise and assignment
		case BITOREQ: // |= bit-wise inclusive or assignment
		case BITXOREQ: // ^= bit-wise exclusive or assignment
			processBitwiseAssign(node);
			break;
		case BITCOMPLEMENT: // ~ bit-wise complement
			processBITCOMPLEMENT(node);
			break;
		case COMMA: // : the comma operator
			processCOMMA(node);
			break;
		case CONDITIONAL: // ?: the conditional operator
			processCONDITIONAL(node);
			break;
		case DEREFERENCE: // * pointer dereference
			processDEREFERENCE(node);
			break;
		case DIVEQ: // /= division assignment
		case MODEQ: // %= integer modulus assignment
		case TIMESEQ: // *= multiplication assignment
			processTIMESEQorDIVEQorMODEQ(node);
			break;
		case EQUALS: // == equality
		case NEQ: // != not equals
			processEqualityOperator(node);
			break;
		case LAND: // && logical and
		case LOR: // || logical or
		case NOT: // ! logical not
		case IMPLIES: // => logical implication
			processLANDorLORorNOT(node);
			break;
		case GT: // > greater than
		case GTE: // >= greater than or equals
		case LT: // < less than
		case LTE: // <= less than or equals
			processRelational(node);
			break;
		case MINUS: // - binary subtraction (numbers and pointers)
			processMINUS(node);
			break;
		case PLUS: // + binary addition: numeric or pointer
			processPLUS(node);
			break;
		case MINUSEQ: // -= subtraction assignment
		case PLUSEQ: // += addition assignment
			processPLUSEQorMINUSEQ(node);
			break;
		case POSTDECREMENT: // -- decrement after expression
		case POSTINCREMENT: // ++ increment after expression
			processPostfixOperators(node);
			break;
		case PREDECREMENT: // -- decrement before expression
		case PREINCREMENT: // ++ increment before expression
			processPrefixOperators(node);
			break;
		case SHIFTLEFT: // << shift left
		case SHIFTRIGHT: // >> shift right
			processSHIFTLEFTorSHIFTRIGHT(node);
			break;
		case SHIFTLEFTEQ: // <<= shift left assignment
		case SHIFTRIGHTEQ: // >>= shift right assignment
			processSHIFTLEFTEQorSHIFTRIGHTEQ(node);
			break;
		case SUBSCRIPT: // [] array subscript
			processSUBSCRIPT(node);
			break;
		case DIV: // / numerical division
		case MOD: // % integer modulus
		case TIMES: // * numeric multiplication
			processTIMESorDIVorMOD(node);
			break;
		case UNARYMINUS: // - numeric negative
		case UNARYPLUS: // + numeric no-op
			processUNARAYPLUSorUNARYMINUS(node);
			break;
		case VALID:
			processValidExpression(node);
			break;
		default:
			throw new RuntimeException("Unknown operator: " + operator);
		}
	}

	private void processHash(OperatorNode node) throws SyntaxException {
		ExpressionNode arg0 = node.getArgument(0);
		ExpressionNode arg1 = node.getArgument(1);
		Type type0 = addStandardConversions(arg0), type1 = addStandardConversions(arg1);

		if (!(type1 instanceof IntegerType))
			throw error(
					"The right-hand-side operand of @ must have integer type",
					arg1);
		node.setInitialType(type0);
	}

	private void processQuantifiedExpression(QuantifiedExpressionNode node)
			throws SyntaxException {
		entityAnalyzer.declarationAnalyzer.processVariableDeclaration(node
				.variable());
		if (node.isRange()) {
			processExpression(node.lower());
			processExpression(node.upper());
		} else {
			processExpression(node.restriction());
		}
		processExpression(node.expression());
		node.setInitialType(typeFactory.basicType(BasicTypeKind.BOOL));
		if (!node.isSideEffectFree(false))
			throw this
					.error("quantified expressions are not allowed to have side effects.",
							node);
	}

	private void processDerivativeExpression(DerivativeExpressionNode node)
			throws SyntaxException {
		ExpressionNode functionNode = node.getFunction();
		Type tmpType;
		TypeKind tmpKind;
		FunctionType functionType;

		processExpression(functionNode);
		tmpType = functionNode.getType();
		tmpKind = tmpType.kind();
		for (int i = 0; i < node.getNumberOfPartials(); i++) {
			processExpression(node.getPartial(i).getRight());
		}
		for (int i = 0; i < node.getNumberOfArguments(); i++) {
			processExpression(node.getArgument(i));
		}
		if (tmpKind == TypeKind.POINTER) {
			tmpType = ((PointerType) tmpType).referencedType();
			tmpKind = tmpType.kind();
		}
		if (tmpKind == TypeKind.FUNCTION)
			functionType = (FunctionType) tmpType;
		else
			throw error(
					"Function expression in derivative expression does not have function "
							+ "type or pointer to function type", functionNode);
		node.setInitialType(functionType.getReturnType());
	}

	private void processSizeof(SizeofNode node) throws SyntaxException {
		SizeableNode argument = node.getArgument();

		if (argument instanceof TypeNode) {
			entityAnalyzer.typeAnalyzer.processTypeNode((TypeNode) argument);
		} else if (argument instanceof ExpressionNode) {
			processExpression((ExpressionNode) argument);
		} else {
			assert false;
		}
		node.setInitialType(typeFactory.size_t());
	}

	private void processRemoteExpression(RemoteExpressionNode node)
			throws SyntaxException {
		ExpressionNode left = node.getProcessExpression();
		IdentifierExpressionNode identifierExpression = node
				.getIdentifierNode();

		processExpression(left);
		processIdentifierExpression(identifierExpression, true, false);
		node.setInitialType(identifierExpression.getInitialType());
	}

	private void processResult(ResultNode node) {
		Function function = entityAnalyzer.enclosingFunction(node);

		node.setInitialType(function.getType().getReturnType());
	}

	// Operators...

	// /**
	// * Given a left hand side expression, try to find the scope in which the
	// * memory object referred to by that expression is stored.
	// *
	// * @param node
	// * a LHS expression node
	// * @return a non-null Scope, in the worst case, the root scope
	// * @throws SyntaxException
	// * if node is not a LHS expression
	// */
	// private Scope scopeOf(ExpressionNode node) throws SyntaxException {
	// Scope result;
	//
	// if (node instanceof IdentifierExpressionNode) {
	// Variable variable = (Variable) ((IdentifierExpressionNode) node)
	// .getIdentifier().getEntity();
	//
	// result = variable.getFirstDeclaration().getScope();
	// } else if (node instanceof OperatorNode) {
	// OperatorNode opNode = (OperatorNode) node;
	// Operator operator = opNode.getOperator();
	//
	// switch (operator) {
	// case DEREFERENCE: {
	// PointerType pointerType = (PointerType) opNode.getArgument(0)
	// .getType();
	//
	// result = entityAnalyzer.rootScope;
	// break;
	// }
	// case SUBSCRIPT:
	// result = scopeOf(((OperatorNode) node).getArgument(0));
	// break;
	// default:
	// throw error("Illegal left-hand side expression", node);
	// }
	// } else if (node instanceof ArrowNode) {
	// // &(e->f) = &((*e).f)
	// ArrowNode arrowNode = (ArrowNode) node;
	// PointerType pointerType = (PointerType) arrowNode
	// .getStructurePointer().getType();
	// ScopeValue scopeValue = pointerType.scopeRestriction();
	//
	// if (scopeValue instanceof Scope)
	// result = (Scope) scopeValue;
	// else
	// result = entityAnalyzer.rootScope;
	// } else if (node instanceof DotNode) { // &(e.f)
	// DotNode dotNode = (DotNode) node;
	// ExpressionNode expr = dotNode.getStructure();
	//
	// result = scopeOf(expr);
	// } else if (node instanceof CompoundLiteralNode) {
	// result = node.getScope();
	// } else if (node instanceof StringLiteralNode) {
	// result = node.getScope();
	// } else
	// throw error("Illegal left-hand side expression", node);
	// return result;
	// }

	private void processADDRESSOF(OperatorNode node) throws SyntaxException {
		ExpressionNode arg0 = node.getArgument(0);

		node.setInitialType(typeFactory.pointerType(arg0.getType()));
	}

	/**
	 * Processes a simple assignment of the form lhs = rhs. Pre-req: the two
	 * operands have already been processed via method
	 * {@link #processExpression}.
	 * 
	 * @param node
	 *            an OperatorNode with operator ASSIGN
	 * @throws SyntaxException
	 *             if there is a type incompatibility between the two sides
	 */
	private void processASSIGN(OperatorNode node) throws SyntaxException {
		ExpressionNode lhs = node.getArgument(0);

		if (!this.isLvalue(lhs)) {
			throw error("The expression " + lhs.prettyRepresentation()
					+ " doesn't designate an object and thus "
					+ "can't be used as the left argument of assignment", node);
		}

		ExpressionNode rhs = node.getArgument(1);
		Type type = assignmentType(node);

		addStandardConversions(rhs);
		try {
			convertRHS(rhs, type);
		} catch (UnsourcedException e) {
			throw error(e, node);
		}
		node.setInitialType(type);
	}

	/**
	 * checks if the given expression is an lvalue.
	 * 
	 * @param node
	 *            the expression to be check
	 */
	private boolean isLvalue(ExpressionNode node) {
		ExpressionKind kind = node.expressionKind();

		switch (kind) {
		case ARROW:
		case DOT:
		case IDENTIFIER_EXPRESSION:
			return true;
		case OPERATOR: {
			OperatorNode operatorNode = (OperatorNode) node;

			switch (operatorNode.getOperator()) {
			case DEREFERENCE:
			case SUBSCRIPT:
				return true;
			default:
			}
		}
		default:
			return false;
		}
	}

	/**
	 * Complete processing of BIG_O node. The operand must be arithmetic, and
	 * the integer promotions are performed. The type is the promoted type.
	 * 
	 */
	private void processBIG_O(OperatorNode node) throws SyntaxException {
		ExpressionNode arg = node.getArgument(0);
		Type type = addStandardConversions(arg);

		if (!(type instanceof ArithmeticType))
			throw error("Argument to unary operator " + node.getOperator()
					+ " has non-arithmetic type: " + type, node);
		if (type instanceof IntegerType)
			type = doIntegerPromotion(arg);
		node.setInitialType(type);
	}

	/**
	 * C11 Sec. 6.5.3.3 says the argument must have integer type, and
	 * 
	 * <blockquote> The result of the ~ operator is the bitwise complement of
	 * its (promoted) operand (that is, each bit in the result is set if and
	 * only if the corresponding bit in the converted operand is not set). The
	 * integer promotions are performed on the operand, and the result has the
	 * promoted type. If the promoted type is an unsigned type, the expression
	 * ~E is equivalent to the maximum value representable in that type minus E.
	 * </blockquote>
	 * 
	 * @param node
	 * @throws SyntaxException
	 */
	private void processBITCOMPLEMENT(OperatorNode node) throws SyntaxException {
		node.setInitialType(doIntegerPromotion(node.getArgument(0)));
	}

	/**
	 * See Sec. 6.5.17.
	 * 
	 * @param node
	 * @throws SyntaxException
	 */
	private void processCOMMA(OperatorNode node) throws SyntaxException {
		node.setInitialType(addStandardConversions(node.getArgument(1)));
	}

	/**
	 * From C11 Sec. 6.5.15:
	 * 
	 * <blockquote> The first operand shall have scalar type.
	 * 
	 * One of the following shall hold for the second and third operands:
	 * <ul>
	 * <li>both operands have arithmetic type;</li>
	 * <li>both operands have the same structure or union type;</li>
	 * <li>both operands have void type;</li>
	 * <li>both operands are pointers to qualified or unqualified versions of
	 * compatible types;</li>
	 * <li>one operand is a pointer and the other is a null pointer constant; or
	 * </li>
	 * <li>one operand is a pointer to an object type and the other is a pointer
	 * to a qualified or unqualified version of void.</li>
	 * </ul>
	 * 
	 * <p>
	 * If both the second and third operands have arithmetic type, the result
	 * type that would be determined by the usual arithmetic conversions, were
	 * they applied to those two operands, is the type of the result. If both
	 * the operands have structure or union type, the result has that type. If
	 * both operands have void type, the result has void type.
	 * </p>
	 * 
	 * <p>
	 * If both the second and third operands are pointers or one is a null
	 * pointer constant and the other is a pointer, the result type is a pointer
	 * to a type qualified with all the type qualifiers of the types referenced
	 * by both operands. Furthermore, if both operands are pointers to
	 * compatible types or to differently qualified versions of compatible
	 * types, the result type is a pointer to an appropriately qualified version
	 * of the composite type; if one operand is a null pointer constant, the
	 * result has the type of the other operand; otherwise, one operand is a
	 * pointer to void or a qualified version of void, in which case the result
	 * type is a pointer to an appropriately qualified version of void.
	 * </p>
	 * 
	 * </blockquote>
	 * 
	 * @param node
	 * @throws SyntaxException
	 */
	private void processCONDITIONAL(OperatorNode node) throws SyntaxException {
		ExpressionNode arg0 = node.getArgument(0);
		ExpressionNode arg1 = node.getArgument(1);
		ExpressionNode arg2 = node.getArgument(2);
		Type type0 = addStandardConversions(arg0);
		Type type1 = addStandardConversions(arg1);
		Type type2 = addStandardConversions(arg2);
		Type type;

		if (!isScalar(type0))
			throw error(
					"First argument of conditional operator has non-scalar type: "
							+ type0, arg0);
		if (type1 instanceof ArithmeticType && type2 instanceof ArithmeticType) {
			type = typeFactory.usualArithmeticConversion(
					(ArithmeticType) type1, (ArithmeticType) type2);
		} else if (type1 instanceof StructureOrUnionType) {
			if (!type1.equals(type2))
				throw error(
						"Operands of conditional operator have incompatible types",
						node);
			type = type1;
		} else if (type1.kind() == TypeKind.VOID
				&& type2.kind() == TypeKind.VOID) {
			type = type1;
		} else if (conversionFactory.isNullPointerConstant(arg1)
				&& type2 instanceof PointerType) {
			type = type2;
		} else if (conversionFactory.isNullPointerConstant(arg2)
				&& type1 instanceof PointerType) {
			type = type1;
		} else if (type1 instanceof PointerType && type2 instanceof PointerType) {
			PointerType p0 = (PointerType) type1;
			PointerType p1 = (PointerType) type2;
			boolean atomicQ = false, constQ = false, volatileQ = false, restrictQ = false;
			Type base0 = p0.referencedType();
			Type base1 = p1.referencedType();

			if (base0 instanceof QualifiedObjectType) {
				QualifiedObjectType q0 = (QualifiedObjectType) base0;

				constQ = q0.isConstQualified();
				volatileQ = q0.isVolatileQualified();
				restrictQ = q0.isRestrictQualified();
				base0 = q0.getBaseType();
			}
			if (base0 instanceof AtomicType) {
				atomicQ = true;
				base0 = ((AtomicType) base0).getBaseType();
			}
			if (base1 instanceof QualifiedObjectType) {
				QualifiedObjectType q1 = (QualifiedObjectType) base1;

				constQ = constQ || q1.isConstQualified();
				volatileQ = volatileQ || q1.isVolatileQualified();
				restrictQ = restrictQ || q1.isRestrictQualified();
				base1 = q1.getBaseType();
			}
			if (base1 instanceof AtomicType) {
				atomicQ = true;
				base1 = ((AtomicType) base1).getBaseType();
			}
			if (base0.kind() == TypeKind.VOID || base1.kind() == TypeKind.VOID)
				type = base0;
			else if (base0.compatibleWith(base1))
				type = typeFactory.compositeType(base0, base1);
			else
				throw error("Incompatible pointer types in conditional:\n"
						+ type1 + "\n" + type2, node);

			type = typeFactory.pointerType(type);
			if (atomicQ)
				type = typeFactory.atomicType((PointerType) type);
			type = typeFactory.qualify((ObjectType) type, constQ, volatileQ,
					restrictQ, false, false);
		} else {
			if (this.config == null
					|| !config.svcomp()
					|| (type1.kind() != TypeKind.VOID && type2.kind() != TypeKind.VOID))
				throw error(
						"Incompatible types for second and third arguments of conditional operator:\n"
								+ type1 + "\n" + type2, node);
			if (type1.kind() == TypeKind.VOID)
				type = type2;
			else
				type = type1;
		}
		node.setInitialType(type);
	}

	/**
	 * Complete processing of PLUS node.
	 * 
	 * Cases: pointer + integer, integer + pointer, arithmetic + arithmetic,
	 * 
	 * TODO: consider actually adding information to the node to say what kind
	 * of addition it is (arithmetic, pointer)
	 * 
	 * @param node
	 */
	private void processPLUS(OperatorNode node) throws SyntaxException {
		ExpressionNode arg0 = node.getArgument(0);
		ExpressionNode arg1 = node.getArgument(1);
		Type type0 = addStandardConversions(arg0);
		Type type1 = addStandardConversions(arg1);

		if (type0.kind() == TypeKind.SCOPE && type1.kind() == TypeKind.SCOPE) {
			// no conversions necessary
			node.setInitialType(type0);
		} else if (type0 instanceof ArithmeticType
				&& type1 instanceof ArithmeticType)
			node.setInitialType(doUsualArithmetic(arg0, arg1));
		else if (isPointerToCompleteObjectType(type0)
				&& type1 instanceof IntegerType)
			node.setInitialType(type0);
		else if (type0 instanceof IntegerType
				&& isPointerToCompleteObjectType(type1))
			node.setInitialType(type1);
		// TODO:experimental:
		else if (isPointerToCompleteObjectType(type0)
				&& type1.kind().equals(TypeKind.RANGE)) {
			node.setInitialType(typeFactory
					.incompleteArrayType((ObjectType) type0));
		} else
			throw error(
					"Invalid arguments for +.  C requires either (1) both arguments\n"
							+ "are numeric, or (2) one argument is numeric and the other is a pointer\n"
							+ "to a complete object type.  The argument types are:\n"
							+ type0 + "\n" + type1, node);
	}

	/**
	 * Processes a binary minus operator expression. From C11 Sec. 6.5.6:
	 * 
	 * <blockquote>
	 * 
	 * For subtraction, one of the following shall hold:
	 * <ul>
	 * <li>both operands have arithmetic type;</li>
	 * <li>both operands are pointers to qualified or unqualified versions of
	 * compatible complete object types; or</li>
	 * <li>the left operand is a pointer to a complete object type and the right
	 * operand has integer type.</li>
	 * </ul>
	 * 
	 * </blockquote>
	 * 
	 * @param node
	 * @throws SyntaxException
	 */
	private void processMINUS(OperatorNode node) throws SyntaxException {
		ExpressionNode arg0 = node.getArgument(0);
		ExpressionNode arg1 = node.getArgument(1);
		Type type0 = addStandardConversions(arg0);
		Type type1 = addStandardConversions(arg1);

		if (type0 instanceof ArithmeticType && type1 instanceof ArithmeticType)
			node.setInitialType(doUsualArithmetic(arg0, arg1));
		else if (isPointerToCompleteObjectType(type0)
				&& type1 instanceof IntegerType)
			node.setInitialType(type0);
		else if (pointerToCompatibleComplete(type0, type1))
			node.setInitialType(typeFactory.ptrdiff_t());
		else
			throw error("Arguments cannot be subtracted", node);
	}

	/**
	 * Processes a += or -= expression. From C11 Sec. 6.5.16.2:
	 * 
	 * <blockquote> For the operators += and -= only, either the left operand
	 * shall be an atomic, qualified, or unqualified pointer to a complete
	 * object type, and the right shall have integer type; or the left operand
	 * shall have atomic, qualified, or unqualified arithmetic type, and the
	 * right shall have arithmetic type. </blockquote>
	 * 
	 * Note: this is almost equivalent to "lhs = lhs + rhs" which results in the
	 * following conversions:
	 * 
	 * <pre>
	 * lhs = (C->L)((L->C)lhs + (R->C)rhs)
	 * </pre>
	 * 
	 * where L is the type of the left hand side (after lvalue conversion), R is
	 * the type of the right hand side (after lvalue conversion) and C is the
	 * type resulting from the "usual arithmetic conversions" applied to L and
	 * R. Hence in the worst case there are 3 conversions, but we don't have a
	 * place to put them all in the unexpanded form (i.e., there's no place for
	 * the L->C conversion since that term is not in the AST).
	 * 
	 * @param node
	 * @throws SyntaxException
	 */
	private void processPLUSEQorMINUSEQ(OperatorNode node)
			throws SyntaxException {
		Type type = assignmentType(node);
		ExpressionNode rhs = node.getArgument(1);
		Type rightType = addStandardConversions(rhs);

		if (isPointerToCompleteObjectType(type)
				&& rightType instanceof IntegerType)
			; // pointer addition: nothing to do
		else if (type instanceof ArithmeticType
				&& rightType instanceof ArithmeticType)
			doArithmeticCompoundAssign((ArithmeticType) type, rhs);
		else
			throw error("Inappropriate arguments to += operator.  "
					+ "Argument types:\n" + type + "\n" + rightType, node);
		node.setInitialType(type);
	}

	private void processTIMESorDIVorMOD(OperatorNode node)
			throws SyntaxException {
		Operator operator = node.getOperator();
		ExpressionNode arg0 = node.getArgument(0);
		ExpressionNode arg1 = node.getArgument(1);
		Type type0 = addStandardConversions(arg0), type1 = addStandardConversions(arg1);

		if (operator == Operator.MOD) {
			if (!(type0 instanceof IntegerType))
				throw error("Arguments to % must have integer type", arg0);
			if (!(type1 instanceof IntegerType))
				throw error("Arguments to % must have integer type", arg1);
		} else {
			if (!(type0 instanceof ArithmeticType))
				throw error("Arguments to " + operator
						+ " must have arithmetic type", arg0);
			if (!(type1 instanceof ArithmeticType))
				throw error("Arguments to " + operator
						+ " must have arithmetic type", arg1);
		}
		node.setInitialType(doUsualArithmetic(arg0, arg1));
	}

	private void processTIMESEQorDIVEQorMODEQ(OperatorNode node)
			throws SyntaxException {
		Operator operator = node.getOperator();
		Type type = assignmentType(node);
		ExpressionNode lhs = node.getArgument(0);
		ExpressionNode rhs = node.getArgument(1);
		Type rightType = addStandardConversions(rhs);

		if (operator == Operator.MOD) {
			if (!(type instanceof IntegerType))
				throw error("Arguments to % must have integer type", lhs);
			if (!(rightType instanceof IntegerType))
				throw error("Arguments to % must have integer type", rhs);
		} else {
			if (!(type instanceof ArithmeticType))
				throw error("Arguments to " + operator
						+ " must have arithmetic type", lhs);
			if (!(rightType instanceof ArithmeticType))
				throw error("Arguments to " + operator
						+ " must have arithmetic type", rhs);
		}
		doArithmeticCompoundAssign((ArithmeticType) type, rhs);
		node.setInitialType(type);
	}

	/**
	 * From C11 Sec. 6.5.7:
	 * 
	 * <blockquote> Each of the operands shall have integer type.
	 * 
	 * The integer promotions are performed on each of the operands. The type of
	 * the result is that of the promoted left operand. If the value of the
	 * right operand is negative or is greater than or equal to the width of the
	 * promoted left operand, the behavior is undefined. </blockquote>
	 * 
	 * @param node
	 */
	private void processSHIFTLEFTorSHIFTRIGHT(OperatorNode node)
			throws SyntaxException {
		node.setInitialType(doIntegerPromotion(node.getArgument(0)));
		doIntegerPromotion(node.getArgument(1));
	}

	/**
	 * Recall from C11 Sec. 6.5.16:
	 * 
	 * <blockquote> An assignment operator stores a value in the object
	 * designated by the left operand. An assignment expression has the value of
	 * the left operand after the assignment, but is not an lvalue. The type of
	 * an assignment expression is the type the left operand would have after
	 * lvalue conversion. The side effect of updating the stored value of the
	 * left operand is sequenced after the value computations of the left and
	 * right operands. The evaluations of the operands are unsequenced.
	 * </blockquote>
	 * 
	 * and
	 * 
	 * <blockquote> For the other operators, the left operand shall have atomic,
	 * qualified, or unqualified arithmetic type, and (considering the type the
	 * left operand would have after lvalue conversion) each operand shall have
	 * arithmetic type consistent with those allowed by the corresponding binary
	 * operator. </blockquote>
	 * 
	 * @param node
	 *            expression node with operator SHIFTLEFTEQ or SHIFTRIGHTEQ
	 * @throws SyntaxException
	 */
	private void processSHIFTLEFTEQorSHIFTRIGHTEQ(OperatorNode node)
			throws SyntaxException {
		Operator operator = node.getOperator();
		ExpressionNode arg0 = node.getArgument(0);
		ExpressionNode arg1 = node.getArgument(1);
		Type type0 = arg0.getConvertedType();
		Conversion conversion;
		Type type;

		if (!(type0 instanceof ObjectType))
			throw error("First argument to " + operator
					+ " has non-object type: " + type0, arg0);
		conversion = conversionFactory.lvalueConversion((ObjectType) type0);
		if (conversion == null)
			type = type0;
		else
			type = conversion.getNewType();
		if (!(type instanceof IntegerType))
			throw error("First argument to " + operator
					+ " has non-integer type: " + type0, arg0);
		addStandardConversions(arg1);
		doIntegerPromotion(arg1);
		node.setInitialType(type);
	}

	/**
	 * C11 Sec. 6.5.8: <blockquote> One of the following shall hold:
	 * <ul>
	 * <li>both operands have real type; or</li>
	 * <li>both operands are pointers to qualified or unqualified versions of
	 * compatible object types.</li>
	 * </ul>
	 * 
	 * If both of the operands have arithmetic type, the usual arithmetic
	 * conversions are performed.
	 * 
	 * Each of the operators < (less than), > (greater than), <= (less than or
	 * equal to), and >= (greater than or equal to) shall yield 1 if the
	 * specified relation is true and 0 if it is false.) The result has type
	 * int. </blockquote>
	 * 
	 * @param node
	 *            an expression node for one of the operators LT, GT, LTE, or
	 *            GTE.
	 */
	private void processRelational(OperatorNode node) throws SyntaxException {
		Operator operator = node.getOperator();
		ExpressionNode arg0 = node.getArgument(0);
		ExpressionNode arg1 = node.getArgument(1);
		Type type0 = addStandardConversions(arg0);
		Type type1 = addStandardConversions(arg1);

		if (type0.kind() == TypeKind.SCOPE && type1.kind() == TypeKind.SCOPE) {
			// no conversions necessary
		} else if (type0 instanceof ArithmeticType
				&& type1 instanceof ArithmeticType) {
			if (!((ArithmeticType) type0).inRealDomain())
				throw error("Argument to relational operator " + operator
						+ " must have real type", arg0);
			if (!((ArithmeticType) type1).inRealDomain())
				throw error("Argument to relational operator " + operator
						+ " must have real type", arg1);
			doUsualArithmetic(arg0, arg1);
		} else if (pointerToCompatibleObject(type0, type1)) {
			// nothing to do
		} else
			throw error("Illegal arguments to operator " + operator, node);
		node.setInitialType(intType);
	}

	/**
	 * 6.5.2.1: "One of the expressions shall have type "pointer to complete
	 * object type", the other expression shall have integer type, and the
	 * result has type "type"."
	 * 
	 * @param node
	 * @throws SyntaxException
	 */
	private void processSUBSCRIPT(OperatorNode node) throws SyntaxException {
		ExpressionNode arg0 = node.getArgument(0);
		ExpressionNode arg1 = node.getArgument(1);
		Type type0 = addStandardConversions(arg0);
		Type type1 = addStandardConversions(arg1);

		if (!(type1 instanceof IntegerType)
				&& !(type1.equals(typeFactory.rangeType()))
				&& !(arg1 instanceof WildcardNode))
			throw error("Subscript does not have integer or range type:\n"
					+ type1, arg1);
		// the following will check pointer in any case
		// if strict C, must also be pointer to complete object type:
		if (isPointerToCompleteObjectType(type0))
			node.setInitialType(((PointerType) type0).referencedType());
		else
			throw error(
					"First argument to subscript operator not pointer to complete object type:\n"
							+ type0, arg0);
	}

	private void processBitwise(OperatorNode node) throws SyntaxException {
		Operator operator = node.getOperator();
		ExpressionNode arg0 = node.getArgument(0);
		ExpressionNode arg1 = node.getArgument(1);
		Type type0 = addStandardConversions(arg0);
		Type type1 = addStandardConversions(arg1);

		if (!(type0 instanceof IntegerType))
			throw error("Argument to bitwise operator " + operator
					+ " must have integer type", arg0);
		if (!(type1 instanceof IntegerType))
			throw error("Argument to bitwise operator " + operator
					+ " must have integer type", arg1);
		node.setInitialType(doUsualArithmetic(arg0, arg1));
	}

	private void processBitwiseAssign(OperatorNode node) throws SyntaxException {
		Operator operator = node.getOperator();
		Type type = assignmentType(node);
		ExpressionNode lhs = node.getArgument(0);
		ExpressionNode rhs = node.getArgument(1);
		Type rightType = addStandardConversions(rhs);

		if (!(type instanceof IntegerType))
			throw error("Argument to bitwise operator " + operator
					+ " must have integer type", lhs);
		if (!(rightType instanceof IntegerType))
			throw error("Argument to bitwise operator " + operator
					+ " must have integer type", rhs);
		doArithmeticCompoundAssign((ArithmeticType) type, rhs);
		node.setInitialType(type);
	}

	/**
	 * Each operand must have "scalar" type, i.e., arithmetic or pointer. Result
	 * has type int (0 or 1).
	 * 
	 * @param node
	 * @throws SyntaxException
	 */
	private void processLANDorLORorNOT(OperatorNode node)
			throws SyntaxException {
		Operator operator = node.getOperator();
		ExpressionNode arg0 = node.getArgument(0);
		Type type0 = addStandardConversions(arg0);

		if (!isScalar(type0))
			throw error("Argument to logical operator " + operator
					+ " does not have scalar type; type is " + type0, arg0);
		if (node.getNumberOfArguments() > 1) {
			ExpressionNode arg1 = node.getArgument(1);
			Type type1 = addStandardConversions(arg1);

			if (!isScalar(type1))
				throw error("Argument to logical operator " + operator
						+ " does not have scalar type; type is " + type1, arg1);
		}
		node.setInitialType(intType);
	}

	/**
	 * 
	 * From C11 Sec. 6.5.9:
	 * 
	 * <blockquote> One of the following shall hold:
	 * <ul>
	 * <li>both operands have arithmetic type;</li>
	 * <li>both operands are pointers to qualified or unqualified versions of
	 * compatible types;</li>
	 * <li>one operand is a pointer to an object type and the other is a pointer
	 * to a qualified or unqualified version of void; or</li>
	 * <li>one operand is a pointer and the other is a null pointer constant.</li>
	 * </ul>
	 * 
	 * <p>
	 * The == (equal to) and != (not equal to) operators are analogous to the
	 * relational operators except for their lower precedence.108) Each of the
	 * operators yields 1 if the specified relation is true and 0 if it is
	 * false. The result has type int. For any pair of operands, exactly one of
	 * the relations is true.
	 * </p>
	 * 
	 * <p>
	 * If both of the operands have arithmetic type, the usual arithmetic
	 * conversions are performed. Values of complex types are equal if and only
	 * if both their real parts are equal and also their imaginary parts are
	 * equal. Any two values of arithmetic types from different type domains are
	 * equal if and only if the results of their conversions to the (complex)
	 * result type determined by the usual arithmetic conversions are equal.
	 * </p>
	 * 
	 * <p>
	 * Otherwise, at least one operand is a pointer. If one operand is a pointer
	 * and the other is a null pointer constant, the null pointer constant is
	 * converted to the type of the pointer. If one operand is a pointer to an
	 * object type and the other is a pointer to a qualified or unqualified
	 * version of void, the former is converted to the type of the latter.
	 * </p>
	 * 
	 * <p>
	 * Two pointers compare equal if and only if both are null pointers, both
	 * are pointers to the same object (including a pointer to an object and a
	 * subobject at its beginning) or function, both are pointers to one past
	 * the last element of the same array object, or one is a pointer to one
	 * past the end of one array object and the other is a pointer to the start
	 * of a different array object that happens to immediately follow the first
	 * array object in the address space.
	 * </p>
	 * 
	 * <p>
	 * For the purposes of these operators, a pointer to an object that is not
	 * an element of an array behaves the same as a pointer to the first element
	 * of an array of length one with the type of the object as its element
	 * type.
	 * </p>
	 * </blockquote>
	 * 
	 * 
	 * @param node
	 */
	private void processEqualityOperator(OperatorNode node)
			throws SyntaxException {
		Operator operator = node.getOperator();
		ExpressionNode arg0 = node.getArgument(0);
		ExpressionNode arg1 = node.getArgument(1);
		Type type0 = addStandardConversions(arg0);
		Type type1 = addStandardConversions(arg1);

		if (type0.kind() == TypeKind.PROCESS
				&& type1.kind() == TypeKind.PROCESS) {
			// no conversions necessary
		} else if (type0.kind() == TypeKind.SCOPE
				&& type1.kind() == TypeKind.SCOPE) {
			// no conversions necessary
		} else if (type0 instanceof ArithmeticType
				&& type1 instanceof ArithmeticType) {
			doUsualArithmetic(arg0, arg1);
		} else if (pointerToCompatibleTypes(type0, type1)) {
			// no conversions necessary
		} else if (type0 instanceof PointerType
				&& conversionFactory.isNullPointerConstant(arg1)) {
			arg1.addConversion(conversionFactory.nullPointerConversion(
					(ObjectType) type1, (PointerType) type0));
		} else if (type1 instanceof PointerType
				&& conversionFactory.isNullPointerConstant(arg0)) {
			arg0.addConversion(conversionFactory.nullPointerConversion(
					(ObjectType) type0, (PointerType) type1));
		} else if (type0 instanceof PointerType && type1 instanceof PointerType) {
			PointerType p0 = (PointerType) type0;
			PointerType p1 = (PointerType) type1;

			if (conversionFactory.isPointerToObject(p0)
					&& conversionFactory.isPointerToVoid(p1)) {
				arg0.addConversion(conversionFactory.voidPointerConversion(p0,
						p1));
			} else if (conversionFactory.isPointerToObject(p1)
					&& conversionFactory.isPointerToVoid(p0)) {
				arg0.addConversion(conversionFactory.voidPointerConversion(p0,
						p1));
			} else
				throw error("Incompatible pointer types for operator "
						+ operator + ":\n" + type0 + "\n" + type1, node);
		} else
			throw error("Incompatible types for operator " + operator + ":\n"
					+ type0 + "\n" + type1, node);
		node.setInitialType(intType);
	}

	/**
	 * In both cases: the operand must be arithmetic, and the integer promotions
	 * are performed. The type is the promoted type.
	 * 
	 * @param node
	 *            expression node for unary + or - operator
	 */
	private void processUNARAYPLUSorUNARYMINUS(OperatorNode node)
			throws SyntaxException {
		Operator operator = node.getOperator();
		ExpressionNode arg = node.getArgument(0);
		Type type = addStandardConversions(arg);

		if (!(type instanceof ArithmeticType))
			throw error("Argument to unary operator " + operator
					+ " has non-arithmetic type: " + type, node);
		if (type instanceof IntegerType)
			type = doIntegerPromotion(arg);
		node.setInitialType(type);
	}

	/**
	 * 
	 * 6.5.2.4.
	 * 
	 * The operand of the postfix increment or decrement operator shall have
	 * atomic, qualified, or unqualified real or pointer type, and shall be a
	 * modifiable lvalue.
	 * 
	 * No lvalue conversion is performed. However, array and function
	 * conversions are performed.
	 * 
	 * @param node
	 */
	private void processPostfixOperators(OperatorNode node)
			throws SyntaxException {
		ExpressionNode arg = node.getArgument(0);
		Type type, baseType;

		addArrayConversion(arg);
		addFunctionConversion(arg);
		type = arg.getConvertedType();
		baseType = stripQualifiers(type);
		if (baseType instanceof ArithmeticType) {
			if (!((ArithmeticType) baseType).inRealDomain())
				throw error("Cannot apply ++ or -- to complex type", node);
		} else if (baseType instanceof PointerType) {
			// nothing to check
		} else
			throw error("Cannot apply ++ or -- to type: " + baseType, node);
		node.setInitialType(type);
	}

	/**
	 * No difference from postfix operators for purposes of type analysis.
	 * 
	 * @param node
	 * @throws SyntaxException
	 */
	private void processPrefixOperators(OperatorNode node)
			throws SyntaxException {
		processPostfixOperators(node);
	}

	private void processDEREFERENCE(OperatorNode node) throws SyntaxException {
		ExpressionNode arg = node.getArgument(0);
		Type type = addStandardConversions(arg);

		if (type instanceof PointerType)
			node.setInitialType(((PointerType) type).referencedType());
		else if (type instanceof ArrayType) {
			ArrayType arrayType = (ArrayType) type;

			if (!(arrayType.getElementType() instanceof PointerType))
				throw error("Argument to * has non-pointer set type: " + type,
						node);
			else
				node.setInitialType(this.typeFactory
						.incompleteArrayType((ObjectType) ((PointerType) arrayType
								.getElementType()).referencedType()));
		} else {
			throw error("Argument to * has non-pointer type: " + type, node);
		}
	}

	private void processRegularRange(RegularRangeNode node)
			throws SyntaxException {
		ExpressionNode low = node.getLow();
		ExpressionNode high = node.getHigh();
		ExpressionNode step = node.getStep();

		processExpression(low);
		doIntegerPromotion(low);
		processExpression(high);
		doIntegerPromotion(high);
		if (step != null) {
			processExpression(step);
			doIntegerPromotion(step);
		}
		node.setInitialType(typeFactory.rangeType());
	}

	/**
	 * Process MPI contract expressions
	 * 
	 * @param node
	 * @throws SyntaxException
	 */
	private void processMPIContractExpression(MPIContractExpressionNode node)
			throws SyntaxException {
		MPIContractExpressionKind kind = node.MPIContractExpressionKind();
		int numArgs = node.numArguments();
		Type[] formalTypes;
		Type exprType;

		if (kind.equals(MPIContractExpressionKind.MPI_INTEGER_CONSTANT)) {
			assert node.getType().equals(intType);
			return;
		}
		formalTypes = new Type[numArgs];
		switch (kind) {
		case MPI_EMPTY_IN:
		case MPI_EMPTY_OUT:
			formalTypes[0] = intType;
			exprType = boolType;
			break;
		case MPI_AGREE:
			formalTypes[0] = null;
			exprType = boolType;
			break;
		case MPI_REGION:
			formalTypes[0] = typeFactory.pointerType(typeFactory.voidType());
			formalTypes[1] = intType;
			formalTypes[2] = intType;
			exprType = typeFactory.voidType();
			break;
		case MPI_EQUALS:
			formalTypes[0] = null;
			formalTypes[1] = intType;
			formalTypes[2] = null;
			formalTypes[3] = null;
			exprType = boolType;
			break;
		default:
			throw error("Unknown MPI contract expression kind: " + kind, node);
		}
		if (numArgs < 1)
			throw error("MPI contract expression " + kind
					+ " takes at least one argument.", node);
		for (int i = 0; i < numArgs; i++) {
			ExpressionNode argument = node.getArgument(i);
			processExpression(argument);
			if (formalTypes[i] != null) {
				if (!argument.getType().equals(formalTypes[i]))
					throw error("The argument in " + i
							+ " position of MPI contract expression " + kind
							+ " must has an " + formalTypes[i], node);
			} else if (i == 0 && kind == MPIContractExpressionKind.MPI_EQUALS) {
				if (argument.getType().compatibleWith(
						typeFactory.pointerType(typeFactory.voidType())))
					throw error("The argument in " + 0
							+ " position of MPI contract expression " + kind
							+ " must has a pointer type", node);
			}

		}
		node.setInitialType(exprType);
	}

	/**
	 * Process <code>\valid( pointer-set )</code> expression. The argument must
	 * has one of the following types:<br>
	 * A pointer type or An array of pointer type.
	 * 
	 * @param node
	 * @throws SyntaxException
	 */
	private void processValidExpression(OperatorNode node)
			throws SyntaxException {
		int numArgs = node.getNumberOfArguments();
		ExpressionNode expr = node.getArgument(0);

		if (numArgs != 1)
			throw error("\\valid(tset) expression only takes one argument",
					node);
		if (expr.getType().kind().equals(TypeKind.ARRAY)) {
			ArrayType arrayType = (ArrayType) expr.getType();

			if (arrayType.getElementType().kind().equals(TypeKind.POINTER)) {
				node.setInitialType(typeFactory.basicType(BasicTypeKind.BOOL));
				return;
			}
		} else if (expr.getType().kind().equals(TypeKind.POINTER)) {
			node.setInitialType(typeFactory.basicType(BasicTypeKind.BOOL));
			return;
		}
		throw error(
				"The argument of a \\valid expression must has an array of pointer type",
				expr);
	}

	// Helper functions...

	private SyntaxException error(String message, ASTNode node) {
		return entityAnalyzer.error(message, node);
	}

	private SyntaxException error(UnsourcedException e, ASTNode node) {
		return entityAnalyzer.error(e, node);
	}

	/**
	 * Given unqualified type, determines whether it is "scalar" (arithmetic or
	 * pointer type).
	 * 
	 * @param type
	 *            unqualified, non-atomic type
	 * @return true if scalar, false otherwise
	 */
	private boolean isScalar(Type type) {
		return type instanceof ArithmeticType || type instanceof PointerType;
	}

	private void addArrayConversion(ExpressionNode node) throws SyntaxException {
		Type oldType = node.getConvertedType();

		if (oldType instanceof ArrayType) {
			Conversion conversion = conversionFactory
					.arrayConversion((ArrayType) oldType);

			node.addConversion(conversion);
		}
	}

	private void addFunctionConversion(ExpressionNode node) {
		Type oldType = node.getConvertedType();

		if (oldType instanceof FunctionType) {
			Conversion conversion = conversionFactory
					.functionConversion((FunctionType) oldType);

			node.addConversion(conversion);
		}
	}

	private void addLvalueConversion(ExpressionNode node) {
		Type oldType = node.getConvertedType();

		if (oldType instanceof ObjectType) {
			Conversion conversion = conversionFactory
					.lvalueConversion((ObjectType) oldType);

			if (conversion != null)
				node.addConversion(conversion);
		}
	}

	/**
	 * Applies array conversion, function conversion, and lvalue conversion to
	 * the given expression. The node is updated as necessary by adding any
	 * nontrivial conversions to the node's conversion list.
	 * 
	 * @param node
	 *            an expression node
	 * @return the post-coversion type of the expression
	 * @throws SyntaxException
	 */
	Type addStandardConversions(ExpressionNode node) throws SyntaxException {
		addArrayConversion(node);
		addFunctionConversion(node);
		addLvalueConversion(node);
		return node.getConvertedType();
	}

	private Type stripQualifiers(Type type) {
		if (type instanceof QualifiedObjectType)
			type = ((QualifiedObjectType) type).getBaseType();
		if (type instanceof AtomicType)
			type = ((AtomicType) type).getBaseType();
		return type;
	}

	/**
	 * Given an unqualified, non-atomic type, tells whether the type is a
	 * pointer to a complete object type.
	 * 
	 * @param type
	 * @return
	 */
	private boolean isPointerToCompleteObjectType(Type type) {
		if (type instanceof PointerType) {
			if (this.language == Language.CIVL_C)
				return true;
			else {
				Type baseType = ((PointerType) type).referencedType();

				if (baseType instanceof ObjectType
						&& ((ObjectType) baseType).isComplete())
					return true;
				else
					return false;
			}
		}
		return false;
	}

	/**
	 * Returns true iff both types are pointer types, and the types pointed to
	 * are qualified or unqualified versions of compatible types.
	 * 
	 * @param type0
	 *            any type
	 * @param type1
	 *            any type
	 * @return true iff condition above holds
	 */
	private boolean pointerToCompatibleTypes(Type type0, Type type1) {
		if (type0 instanceof PointerType && type1 instanceof PointerType) {
			Type base0 = stripQualifiers(((PointerType) type0).referencedType());
			Type base1 = stripQualifiers(((PointerType) type1).referencedType());

			return base0.compatibleWith(base1);
		}
		return false;
	}

	/**
	 * Returns true iff both types are pointer types, and the types pointed to
	 * are qualified or unqualified versions of compatible object types.
	 * 
	 * @param type0
	 *            any type
	 * @param type1
	 *            any type
	 * @return true iff condition above holds
	 */
	private boolean pointerToCompatibleObject(Type type0, Type type1) {
		if (type0 instanceof PointerType && type1 instanceof PointerType) {
			Type base0 = stripQualifiers(((PointerType) type0).referencedType());
			Type base1 = stripQualifiers(((PointerType) type1).referencedType());

			return base0 instanceof ObjectType && base1 instanceof ObjectType
					&& base0.compatibleWith(base1);
		}
		return false;
	}

	/**
	 * Returns true iff both types are pointer types, and the types pointed to
	 * are qualified or unqualified versions of compatible complete object
	 * types.
	 * 
	 * @param type0
	 *            any type
	 * @param type1
	 *            any type
	 * @return true iff condition above holds
	 */
	private boolean pointerToCompatibleComplete(Type type0, Type type1) {
		if (type0 instanceof PointerType && type1 instanceof PointerType) {
			Type base0 = stripQualifiers(((PointerType) type0).referencedType());
			Type base1 = stripQualifiers(((PointerType) type1).referencedType());

			return base0 instanceof ObjectType && base1 instanceof ObjectType
					&& ((ObjectType) base0).isComplete()
					&& ((ObjectType) base1).isComplete()
					&& base0.compatibleWith(base1);
		}
		return false;
	}

	/**
	 * Given two expression with arithmetic type, computes the common type
	 * resulting from the "usual arithmetic conversions", adds conversions as
	 * needed to the two expressions, and returns the common type.
	 * 
	 * This method does not perform the standard conversions (lvalue, array,
	 * function). If you want those, do them first, then invoke this method.
	 * 
	 * @param arg0
	 *            expression of arithmetic type
	 * @param arg1
	 *            expression of arithmetic type
	 * @return the common type resulting from the usual arithmetic conversions
	 */
	private ArithmeticType doUsualArithmetic(ExpressionNode arg0,
			ExpressionNode arg1) {
		ArithmeticType a0 = (ArithmeticType) arg0.getConvertedType();
		ArithmeticType a1 = (ArithmeticType) arg1.getConvertedType();
		ArithmeticType type = typeFactory.usualArithmeticConversion(a0, a1);

		if (!type.equals(a0))
			arg0.addConversion(conversionFactory.arithmeticConversion(a0, type));
		if (!type.equals(a1))
			arg1.addConversion(conversionFactory.arithmeticConversion(a1, type));
		return type;
	}

	/**
	 * Given an assignment expression (for a simple or compound assignment),
	 * this method computes the type of the expression. The type of the
	 * expression is the result of applying lvalue conversion to the left hand
	 * side. The expression is not modified.
	 * 
	 * <blockquote> 6.3.2.1 Lvalues, arrays, and function designators <br>
	 * 1. An lvalue is an expression (with an object type other than void) that
	 * potentially designates an object;64) if an lvalue does not designate an
	 * object when it is evaluated, the behavior is undefined. When an object is
	 * said to have a particular type, the type is specified by the lvalue used
	 * to designate the object. A modifiable lvalue is an lvalue that does not
	 * have array type, does not have an incomplete type, does not have a const-
	 * qualified type, and if it is a structure or union, does not have any
	 * member (including, recursively, any member or element of all contained
	 * aggregates or unions) with a const-qualified type. </blockquote>
	 * 
	 * @param assignExpression
	 * @return the type of the assignment expression
	 * @throws SyntaxException
	 *             if the type of the left hand side is not an object type
	 */
	private Type assignmentType(OperatorNode assignExpression)
			throws SyntaxException {
		ExpressionNode leftNode = assignExpression.getArgument(0);
		Type leftType = leftNode.getType();
		Conversion leftConversion;

		if (typeFactory.isVoidType(leftType))
			throw error("Left argument of assignment can't have void type",
					leftNode);
		if (!(leftType instanceof ObjectType))
			throw error(
					"Left argument of assignment does not have object type",
					leftNode);
		if (leftType instanceof ArrayType)
			throw error("Left argument of assignment can't have array type",
					leftNode);

		ObjectType objectType = (ObjectType) leftType;

		// if (!this.typeFactory.isBundleType(objectType)
		// && !objectType.isComplete())
		// throw error(
		// "Type of the left argument of assignment can't be incomplete",
		// leftNode);
		if (objectType instanceof QualifiedObjectType) {
			if (((QualifiedObjectType) objectType).isInputQualified())
				throw error(
						"Type of the left argument of assignment has input-qualifier",
						leftNode);
		}
		if (objectType.isConstantQualified())
			throw error(
					"Type of the left argument of assignment has const-qualifier",
					leftNode);
		leftConversion = conversionFactory
				.lvalueConversion((ObjectType) leftType);
		return leftConversion == null ? leftType : leftConversion.getNewType();
	}

	/**
	 * Given (1) the type of a (simple or compound) assignment expression, and
	 * (2) the right hand side argument of that assignment expression, this
	 * method adds an implicit arithmetic conversion to the rhs argument if one
	 * is needed. The conversion is to the type resulting from applying the
	 * "usual arithmetic conversions" to the two types.
	 * 
	 * Recall that the type of an assignment expression if the type that results
	 * from applying lvalue conversion to the left hand side.
	 * 
	 * @param assignmentType
	 *            the type of the assignment expression
	 * @param rightNode
	 *            the right hand side argument of the assignment expression
	 */
	private void doArithmeticCompoundAssign(ArithmeticType assignmentType,
			ExpressionNode rightNode) {
		ArithmeticType a1 = (ArithmeticType) rightNode.getConvertedType();
		ArithmeticType commonType = typeFactory.usualArithmeticConversion(
				assignmentType, a1);

		if (!commonType.equals(a1))
			rightNode.addConversion(conversionFactory.arithmeticConversion(a1,
					commonType));
	}

	private void convertRHS(ExpressionNode rightNode, Type type)
			throws UnsourcedException {
		Conversion rightConversion = conversionFactory.assignmentConversion(
				config, rightNode, type);

		if (rightConversion != null)
			rightNode.addConversion(rightConversion);
	}

	/**
	 * Given an expression node of integer type, performs the standard
	 * conversions and then the integer promotion, adding conversions as
	 * necessary to the node.
	 * 
	 * @param node
	 *            an expression node
	 * @return the post-conversion type of the expression
	 * @throws SyntaxException
	 *             if the node does not have integer type
	 */
	private IntegerType doIntegerPromotion(ExpressionNode node)
			throws SyntaxException {
		Type type = addStandardConversions(node);

		if (type instanceof IntegerType) {
			IntegerType promotedType = typeFactory
					.integerPromotion((IntegerType) type);

			if (promotedType.equals(type))
				return (IntegerType) type;
			else {
				node.addConversion(conversionFactory.arithmeticConversion(
						(IntegerType) type, promotedType));
				return promotedType;
			}
		} else {
			throw error("Expected expression of integer type", node);
		}
	}
}
