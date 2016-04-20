package edu.udel.cis.vsl.abc.analysis.entity;

import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.abc.ast.entity.IF.Entity.EntityKind;
import edu.udel.cis.vsl.abc.ast.entity.IF.OrdinaryEntity;
import edu.udel.cis.vsl.abc.ast.entity.IF.Scope;
import edu.udel.cis.vsl.abc.ast.entity.IF.Scope.ScopeKind;
import edu.udel.cis.vsl.abc.ast.entity.IF.TaggedEntity;
import edu.udel.cis.vsl.abc.ast.entity.IF.Typedef;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.NodeFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.EnumeratorDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FieldDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.ArrayTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.AtomicTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.BasicTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.DomainTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.EnumerationTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.FunctionTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.PointerTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.StructureOrUnionTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode.TypeNodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypedefNameNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeofNode;
import edu.udel.cis.vsl.abc.ast.type.IF.ArrayType;
import edu.udel.cis.vsl.abc.ast.type.IF.DomainType;
import edu.udel.cis.vsl.abc.ast.type.IF.EnumerationType;
import edu.udel.cis.vsl.abc.ast.type.IF.Enumerator;
import edu.udel.cis.vsl.abc.ast.type.IF.Field;
import edu.udel.cis.vsl.abc.ast.type.IF.IntegerType;
import edu.udel.cis.vsl.abc.ast.type.IF.ObjectType;
import edu.udel.cis.vsl.abc.ast.type.IF.PointerType;
import edu.udel.cis.vsl.abc.ast.type.IF.QualifiedObjectType;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.StructureOrUnionType;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.ast.type.IF.Type.TypeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.TypeFactory;
import edu.udel.cis.vsl.abc.ast.type.IF.UnqualifiedObjectType;
import edu.udel.cis.vsl.abc.ast.value.IF.IntegerValue;
import edu.udel.cis.vsl.abc.ast.value.IF.Value;
import edu.udel.cis.vsl.abc.ast.value.IF.ValueFactory;
import edu.udel.cis.vsl.abc.config.IF.Configurations.Language;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.token.IF.UnsourcedException;

/**
 * Analyzes types nodes in the AST, sets the type of the type node and processes
 * all children.
 * 
 * @author siegel
 * 
 */
public class TypeAnalyzer {

	// ***************************** Fields *******************************

	private EntityAnalyzer entityAnalyzer;

	private TypeFactory typeFactory;

	private NodeFactory nodeFactory;

	private ValueFactory valueFactory;

	// private Configuration configuration;
	private Language language;

	/**
	 * The type used for enumerators, i.e., the elements of enumeration types.
	 * It is an unspecified integer type according to the C Standard.
	 */
	private IntegerType enumeratorType;

	// ************************** Constructors ****************************

	TypeAnalyzer(EntityAnalyzer entityAnalyzer, TypeFactory typeFactory) {
		this.entityAnalyzer = entityAnalyzer;
		this.nodeFactory = entityAnalyzer.nodeFactory;
		this.typeFactory = typeFactory;
		this.valueFactory = entityAnalyzer.valueFactory;
		this.enumeratorType = (IntegerType) typeFactory
				.basicType(BasicTypeKind.INT);
		this.language = entityAnalyzer.language;
	}

	// ************************** Private Methods **************************

	private SyntaxException error(String message, ASTNode node) {
		return entityAnalyzer.error(message, node);
	}

	private SyntaxException error(UnsourcedException e, ASTNode node) {
		return entityAnalyzer.error(e, node);
	}

	private Type processBasicType(BasicTypeNode node) throws SyntaxException {
		UnqualifiedObjectType unqualifiedType = typeFactory.basicType(node
				.getBasicTypeKind());
		boolean constQ = node.isConstQualified();
		boolean volatileQ = node.isVolatileQualified();
		boolean inputQ = node.isInputQualified();
		boolean outputQ = node.isOutputQualified();

		if (node.isRestrictQualified())
			throw error("restrict qualifier used with basic type", node);
		if (node.isAtomicQualified())
			unqualifiedType = typeFactory.atomicType(unqualifiedType);
		if (constQ || volatileQ || inputQ || outputQ)
			return typeFactory.qualifiedType(unqualifiedType, constQ,
					volatileQ, false, inputQ, outputQ);
		else
			return unqualifiedType;
	}

	/**
	 * 
	 * C11 6.7.6.2(1): "The element type shall not be an incomplete or function
	 * type. The optional type qualifiers and the keyword static shall appear
	 * only in a declaration of a function parameter with an array type, and
	 * then only in the outermost array type derivation."
	 * 
	 * @param node
	 * @return
	 * @throws SyntaxException
	 */
	private ObjectType processArrayType(ArrayTypeNode node, boolean isParameter)
			throws SyntaxException {
		TypeNode elementTypeNode = node.getElementType(); // non-null
		Type tempElementType = processTypeNode(elementTypeNode);
		ObjectType elementType;
		ExpressionNode sizeExpression;
		boolean constQ = node.isConstQualified();
		boolean volatileQ = node.isVolatileQualified();
		boolean restrictQ = node.isRestrictQualified();
		boolean inputQ = node.isInputQualified();
		boolean outputQ = node.isOutputQualified();
		ObjectType result;

		if (!(tempElementType instanceof ObjectType))
			throw error("Non-object type used for element type of array type",
					elementTypeNode);
		elementType = (ObjectType) tempElementType;
		if (this.language == Language.C && !isParameter
				&& !elementType.isComplete())
			throw error("Element type of array type is not complete",
					elementTypeNode);
		// C11 6.7.3(3):
		// "The type modified by the _Atomic qualifier shall not be an
		// array type or a function type."
		if (node.isAtomicQualified())
			throw error("_Atomic qualifier used with array type", node);
		// C11 6.7.3(9):
		// "If the specification of an array type includes any type qualifiers,
		// the element type is so-qualified, not the array type."
		// but don't apply that rule to $input and $output
		elementType = typeFactory.qualify(elementType, constQ, volatileQ,
				restrictQ, false, false);
		if (restrictQ
				&& elementType instanceof QualifiedObjectType
				&& ((QualifiedObjectType) elementType).getBaseType().kind() != TypeKind.POINTER)
			throw error("Use of restrict qualifier with non-pointer type", node);
		if (isParameter) {
			// no scope restriction on pointer given, so use null...
			PointerType pointerType = typeFactory.pointerType(elementType);
			UnqualifiedObjectType unqualifiedType = (node.hasAtomicInBrackets() ? typeFactory
					.atomicType(pointerType) : pointerType);

			// need to process size expression, but ignore it...
			sizeExpression = node.getExtent();
			if (sizeExpression != null)
				entityAnalyzer.expressionAnalyzer
						.processExpression(sizeExpression);
			return typeFactory.qualify(unqualifiedType,
					node.hasConstInBrackets(), node.hasVolatileInBrackets(),
					node.hasRestrictInBrackets(), false, false);
		}
		if (node.hasAtomicInBrackets() || node.hasConstInBrackets()
				|| node.hasVolatileInBrackets() || node.hasRestrictInBrackets())
			throw error("Type qualifiers in [...] in an array declarator "
					+ "can only appear in a parameter declaration",
					elementTypeNode);
		if (node.hasUnspecifiedVariableLength()) { // "*"
			result = typeFactory
					.unspecifiedVariableLengthArrayType(elementType);
		} else {
			sizeExpression = node.getExtent();
			if (sizeExpression == null) {
				result = typeFactory.incompleteArrayType(elementType);
			} else {
				entityAnalyzer.expressionAnalyzer
						.processExpression(sizeExpression);
				if (sizeExpression.isConstantExpression()) {
					result = typeFactory.arrayType(elementType,
							(IntegerValue) nodeFactory
									.getConstantValue(sizeExpression));
				} else {
					// C11 6.7.6.2(5): "If the size is an expression that is not
					// an integer constant expression: if it occurs in a
					// declaration at function prototype scope, it is treated as
					// if it were replaced by *"
					if (node.getScope().getScopeKind() == ScopeKind.FUNCTION_PROTOTYPE)
						result = typeFactory
								.unspecifiedVariableLengthArrayType(elementType);
					else
						result = typeFactory.variableLengthArrayType(
								elementType, sizeExpression);
				}
			}
		}
		if (inputQ || outputQ)
			result = typeFactory.qualify(result, false, false, false, inputQ,
					outputQ);
		return result;
	}

	private Type processPointerType(PointerTypeNode node)
			throws SyntaxException {
		TypeNode referencedTypeNode = node.referencedType();
		Type referencedType = processTypeNode(referencedTypeNode);
		UnqualifiedObjectType unqualifiedType = typeFactory
				.pointerType(referencedType);

		if (node.isAtomicQualified())
			unqualifiedType = typeFactory.atomicType(unqualifiedType);
		return typeFactory.qualify(unqualifiedType, node.isConstQualified(),
				node.isVolatileQualified(), node.isRestrictQualified(),
				node.isInputQualified(), node.isOutputQualified());
	}

	private Type processAtomicType(AtomicTypeNode node) throws SyntaxException {
		// C11 6.7.2.4(3): "The type name in an atomic type specifier shall not
		// refer to an array type, a function type, an atomic type, or a
		// qualified type."
		Type baseType = processTypeNode(node.getBaseType());
		TypeKind kind = baseType.kind();

		if (kind == TypeKind.ARRAY)
			throw error(
					"Type name used in atomic type specifier refers to an array type",
					node);
		if (kind == TypeKind.FUNCTION)
			throw error(
					"Type name used in atomic type specifier refers to a function type",
					node);
		if (kind == TypeKind.ATOMIC)
			throw error(
					"Type name used in atomic type specifier refers to an atomic type",
					node);
		if (kind == TypeKind.QUALIFIED)
			throw error(
					"Type name used in atomic type specifier refers to a qualified type",
					node);
		return typeFactory.atomicType((UnqualifiedObjectType) baseType);
	}

	private Type processTypedefName(TypedefNameNode typeNode,
			boolean isParameter) throws SyntaxException {
		String name = typeNode.getName().name();
		Scope scope = typeNode.getScope();
		OrdinaryEntity entity = scope.getLexicalOrdinaryEntity(true, name);
		EntityKind kind = entity.getEntityKind();
		Typedef typedef;
		Type result;

		if (kind != EntityKind.TYPEDEF)
			throw error(
					"Internal error: typedef name does not refer to typedef",
					typeNode);
		typedef = (Typedef) entity;
		typeNode.getName().setEntity(typedef);
		result = typedef.getType();
		if (isParameter && result.kind() == TypeKind.ARRAY) {
			result = typeFactory.pointerType(((ArrayType) result)
					.getElementType());
		}
		return result;
	}

	private boolean onlyVoid(SequenceNode<VariableDeclarationNode> parameters) {
		if (parameters.numChildren() == 1) {
			VariableDeclarationNode decl = parameters.getSequenceChild(0);

			if (decl != null && decl.getIdentifier() == null) {
				TypeNode typeNode = decl.getTypeNode();

				return typeNode != null && typeNode.kind() == TypeNodeKind.VOID
						&& !typeNode.isAtomicQualified()
						&& !typeNode.isConstQualified()
						&& !typeNode.isRestrictQualified()
						&& !typeNode.isVolatileQualified();
			}
		}
		return false;
	}

	private void checkNoAlignments(VariableDeclarationNode node)
			throws SyntaxException {
		SequenceNode<ExpressionNode> seq1 = node.constantAlignmentSpecifiers();

		if (seq1 != null && seq1.numChildren() > 0) {
			ExpressionNode alignment = seq1.getSequenceChild(0);

			throw error(
					"Alignment attribute in parameter declaration; see C11 6.7.5(2)",
					alignment);
		}

		SequenceNode<TypeNode> seq2 = node.typeAlignmentSpecifiers();

		if (seq2 != null && seq2.numChildren() > 0) {
			TypeNode alignment = seq2.getSequenceChild(0);

			throw error(
					"Alignment attribute in parameter declaration; see C11 6.7.5(2)",
					alignment);
		}
	}

	private Type processFunctionType(FunctionTypeNode node, boolean isParameter)
			throws SyntaxException {
		Type result;
		TypeNode returnTypeNode = node.getReturnType();
		SequenceNode<VariableDeclarationNode> parameters = node.getParameters();
		int numParameters = parameters.numChildren();
		boolean isDefinition = node.parent() instanceof FunctionDefinitionNode;
		boolean fromIdentifierList = node.hasIdentifierList();
		boolean hasVariableArgs = node.hasVariableArgs();
		Type tempReturnType = processTypeNode(returnTypeNode);
		ObjectType returnType;

		// "A function declarator shall not specify a return type that is a
		// function type or an array type."
		if (!(tempReturnType instanceof ObjectType))
			throw error(
					"Return type in function declaration is not an object type",
					returnTypeNode);
		if (tempReturnType instanceof ArrayType)
			throw error("Return type in function declaration is an array type",
					returnTypeNode);
		returnType = (ObjectType) tempReturnType;
		if (fromIdentifierList && !isDefinition && numParameters == 0) {
			// no information known about parameters
			result = typeFactory.functionType(returnType);
		} else {
			List<ObjectType> parameterTypes = new LinkedList<ObjectType>();

			if (hasVariableArgs || !onlyVoid(parameters)) {
				for (VariableDeclarationNode decl : parameters) {
					TypeNode parameterTypeNode;

					// C11 6.7.5(2): "An alignment attribute shall not be
					// specified in a declaration of a typedef, or a bit-field,
					// or a function, or a parameter, or an object declared
					// with the register storage-class specifier."
					checkNoAlignments(decl);
					// C11 6.7.6.3(2): "The only storage-class specifier that
					// shall occur in a parameter declaration is register."
					// the others are extern, static, _Thread_local, auto
					if (decl.hasExternStorage() || decl.hasStaticStorage()
							|| decl.hasThreadLocalStorage())
						throw error(
								"Illegal storage class specified in parameter declaration; see C11 6.7.6.3(2)",
								decl);
					entityAnalyzer.declarationAnalyzer
							.processVariableDeclaration(decl, true);
					parameterTypeNode = decl.getTypeNode();
					if (parameterTypeNode == null)
						throw error("No type specified for function parameter",
								decl);
					parameterTypes
							.add((ObjectType) parameterTypeNode.getType());
				}
			}
			result = typeFactory.functionType(returnType, fromIdentifierList,
					parameterTypes, hasVariableArgs);
		}
		if (isParameter)
			result = typeFactory.pointerType(result);
		return result;
	}

	/**
	 * Creates new enumeration entity and type and adds them to the scope of the
	 * given node.
	 * 
	 * @param node
	 *            an enumeration type node with non-null enumerators
	 * @return the new enumeration entity
	 * @throws SyntaxException
	 */
	private EnumerationType createEnumeration(EnumerationTypeNode node)
			throws SyntaxException {
		SequenceNode<EnumeratorDeclarationNode> enumerators = node
				.enumerators();
		Scope scope = node.getScope();
		String tag = node.getName(); // could be null
		List<Enumerator> enumeratorList = new LinkedList<>();
		EnumerationType enumerationType = typeFactory
				.enumerationType(node, tag);
		IntegerValue value = null;

		// clear it, in case it was used in previous analysis pass
		enumerationType.clear();
		scope.add(enumerationType);
		enumerationType.setDefinition(node);
		enumerationType.addDeclaration(node);
		for (EnumeratorDeclarationNode decl : enumerators) {
			ExpressionNode constantNode = decl.getValue();
			Enumerator enumerator;

			if (constantNode == null) {
				if (value == null)
					value = valueFactory.integerValue(enumeratorType, 0);
				else
					value = valueFactory.plusOne(value);
			} else {
				Value tmpValue;

				entityAnalyzer.expressionAnalyzer
						.processExpression(constantNode);
				if (!constantNode.isConstantExpression())
					throw error(
							"Non-constant expression used in enumerator definition",
							constantNode);
				tmpValue = nodeFactory.getConstantValue(constantNode);
				if (!(tmpValue instanceof IntegerValue))
					throw error(
							"Constant expression of concrete integer type expected, not "
									+ tmpValue, constantNode);
				value = (IntegerValue) tmpValue;
			}
			enumerator = typeFactory
					.newEnumerator(decl, enumerationType, value);
			enumerator.addDeclaration(decl);
			enumerator.setDefinition(decl);
			decl.setEntity(enumerator);
			decl.getIdentifier().setEntity(enumerator);
			enumeratorList.add(enumerator);
			try {
				scope.add(enumerator);
			} catch (UnsourcedException e) {
				throw error(e, decl);
			}
		}
		enumerationType.complete(enumeratorList);
		return enumerationType;
	}

	/**
	 * Creates a new structure or union entity and type based on given node.
	 * Adds it to the scope. This method should only be called if it is known no
	 * such entity exists.
	 * 
	 * @param node
	 *            a structure or union node
	 * @return the resulting structure or union entity
	 * @throws SyntaxException
	 *             if already exists in scope
	 */
	private StructureOrUnionType createStructureOrUnion(
			StructureOrUnionTypeNode node) throws SyntaxException {
		Scope scope = node.getScope();
		IdentifierNode identifier = node.getIdentifier();
		String tag = node.getName(); // could be null
		SequenceNode<FieldDeclarationNode> fieldDecls = node
				.getStructDeclList(); // could be null
		StructureOrUnionType structureOrUnionType = typeFactory
				.structureOrUnionType(node, node.isStruct(), tag);

		// in case this was used in previous analysis pass, clear it:
		structureOrUnionType.clear();
		scope.add(structureOrUnionType);
		if (identifier != null)
			identifier.setEntity(structureOrUnionType);
		if (fieldDecls != null) {
			completeStructOrUnion(structureOrUnionType, node);
		}
		return structureOrUnionType;
	}

	/**
	 * Checks that an existing tagged entity <code>old</code> is consistent with
	 * one defined by a given structure or union type node <code>node</code>.
	 * Consistency entails:
	 * <ul>
	 * <li>if <code>node</code> defines a struct, <code>old</code> is a struct;
	 * if <code>node</code> defines a union, <code>old</code> is a union</li>
	 * <li>at least one of <code>old</code> and <code>node</code> is incomplete,
	 * i.e., does not contain the field declarations</li>
	 * </ul>
	 * 
	 * @param old
	 *            an existing tagged entity (non-<code>null</code>)
	 * @param node
	 *            a structure or union type node (non-<code>null</code>)
	 * @throws SyntaxException
	 *             if the existing entity and the node are inconsistent
	 */
	private void checkConsistency(TaggedEntity old,
			StructureOrUnionTypeNode node) throws SyntaxException {
		String tag = node.getName();
		StructureOrUnionType su;

		if (old.getEntityKind() != EntityKind.STRUCTURE_OR_UNION)
			throw error("Re-use of tag " + tag
					+ " for structure or union.  Previous use was at "
					+ old.getFirstDeclaration().getSource(), node);
		su = (StructureOrUnionType) old;
		if (su.isStruct()) {
			if (!node.isStruct())
				throw error("Previous use of tag " + tag
						+ " was for structure, current use for union. "
						+ "Previous use was at "
						+ old.getFirstDeclaration().getSource(), node);
		} else {
			if (node.isStruct())
				throw error("Previous use of tag " + tag
						+ " was for union, current use for structure. "
						+ "Previous use was at "
						+ old.getFirstDeclaration().getSource(), node);
		}
		if (su.getType().isComplete() && node.getStructDeclList() != null)
			throw error(
					"Re-definition of structure or union.  Previous definition at "
							+ old.getFirstDeclaration().getSource(), node);
	}

	/**
	 * Given an incomplete structure or union entity and a consistent, complete
	 * structure or union type node, completes the entity using the information
	 * provided by the node.
	 * 
	 * @param structureOrUnion
	 *            an incomplete structure or union entity (non-<code>null</code>
	 *            )
	 * @param node
	 *            a complete structure or union type node consistent with the
	 *            <code>structureOrUnion</code> (non-<code>null</code>)
	 * @throws SyntaxException
	 *             if a field is declared with a non-object type or bit width is
	 *             specified with a non-constant expression
	 * @see {@link #checkConsistency(TaggedEntity, StructureOrUnionTypeNode)}
	 */
	private void completeStructOrUnion(
			StructureOrUnionType structureOrUnionType,
			StructureOrUnionTypeNode node) throws SyntaxException {
		SequenceNode<FieldDeclarationNode> fieldDecls = node
				.getStructDeclList();
		List<Field> fieldList = new LinkedList<>();

		structureOrUnionType.setDefinition(node);
		for (FieldDeclarationNode decl : fieldDecls) {
			TypeNode fieldTypeNode = decl.getTypeNode();
			ExpressionNode bitWidthExpression = decl.getBitFieldWidth();
			Value bitWidth;
			ObjectType fieldType;
			Field field;

			if (fieldTypeNode == null)
				fieldType = null;
			else {
				Type tempType = processTypeNode(fieldTypeNode);

				if (!(tempType instanceof ObjectType))
					throw error(
							"Non-object type for structure or union member",
							fieldTypeNode);
				fieldType = (ObjectType) tempType;
			}
			if (bitWidthExpression == null) {
				bitWidth = null;
			} else {
				if (!bitWidthExpression.isConstantExpression())
					throw error(
							"Non-constant expression used for bit width in field declaration",
							bitWidthExpression);
				bitWidth = nodeFactory.getConstantValue(bitWidthExpression);
			}
			field = typeFactory.newField(decl, fieldType, bitWidth
			// ,structureOrUnion
					);
			decl.setEntity(field);
			if (decl.getIdentifier() != null)
				decl.getIdentifier().setEntity(field);
			fieldList.add(field);
		}
		structureOrUnionType.complete(fieldList);
	}

	/**
	 * Processes a domain type node. Such a node is specified in source form by
	 * <code>$domain</code> or <code>$domain(expr)</code>, where
	 * <code>expr</code> is a constant expression of integer type
	 * 
	 * @param node
	 *            a domain type node (non-<code>null</code>)
	 * @return the domain type specified by the node
	 * @throws SyntaxException
	 *             if the dimension expression is present but does not have
	 *             integer type or is not a constant expression
	 */
	private DomainType processDomainType(DomainTypeNode node)
			throws SyntaxException {
		ExpressionNode dimensionNode = node.getDimension();
		DomainType result;

		if (dimensionNode != null) {
			Value value;

			entityAnalyzer.expressionAnalyzer.processExpression(dimensionNode);
			value = nodeFactory.getConstantValue(dimensionNode);
			if (value == null || !(value instanceof IntegerValue))
				throw error("$domain requires constant integer argument", node);
			else {
				IntegerValue integerValue = (IntegerValue) value;
				int dimension = integerValue.getIntegerValue().intValue();

				result = typeFactory.domainType(dimension);
			}
		} else
			result = typeFactory.domainType();
		return result;
	}

	// ************************* Exported Methods **************************

	/**
	 * Processes a type node and sets the type field of that type node to the
	 * type computed from the type node.
	 * 
	 * @param typeNode
	 *            a type node which may or may not have been processed already
	 * @return the type computed from the type node
	 * @throws SyntaxException
	 *             if there is a syntax problem with the type node
	 */
	Type processTypeNode(TypeNode typeNode) throws SyntaxException {
		return processTypeNode(typeNode, false);
	}

	/**
	 * <p>
	 * Processes a {@link TypeNode}. The Type defined by that type node is
	 * computed and associated to the TypeNode.
	 * </p>
	 * 
	 * <p>
	 * This method may also entail the creation and/or modification of entities.
	 * For example, if the type node defines a strucuture or union type, or
	 * enumeration type, then the corresponding entities may be created or
	 * completed.
	 * </p>
	 * 
	 * @param typeNode
	 *            a non-<code>null</code> type node
	 * @return the type specified by that node
	 * @throws SyntaxException
	 *             if any static errors are detected in the processing of the
	 *             type node
	 */
	Type processTypeNode(TypeNode typeNode, boolean isParameter)
			throws SyntaxException {
		TypeNodeKind kind = typeNode.kind();
		Type type;

		switch (kind) {
		case VOID:
			type = typeFactory.voidType();
			break;
		case BASIC:
			type = processBasicType((BasicTypeNode) typeNode);
			break;
		case ENUMERATION:
			type = processEnumerationType((EnumerationTypeNode) typeNode);
			break;
		case ARRAY:
			type = processArrayType((ArrayTypeNode) typeNode, isParameter);
			break;
		case STRUCTURE_OR_UNION:
			type = processStructureOrUnionType((StructureOrUnionTypeNode) typeNode);
			break;
		case FUNCTION:
			type = processFunctionType((FunctionTypeNode) typeNode, isParameter);
			break;
		case POINTER:
			type = processPointerType((PointerTypeNode) typeNode);
			break;
		case ATOMIC:
			type = processAtomicType((AtomicTypeNode) typeNode);
			break;
		case TYPEDEF_NAME:
			type = processTypedefName((TypedefNameNode) typeNode, isParameter);
			break;
		case SCOPE:
			type = typeFactory.scopeType();
			break;
		case DOMAIN:
			type = processDomainType((DomainTypeNode) typeNode);
			break;
		case RANGE:
			type = typeFactory.rangeType();
			break;
		case TYPEOF: {
			ExpressionNode expression = ((TypeofNode) typeNode)
					.getExpressionOperand();
			entityAnalyzer.expressionAnalyzer.processExpression(expression);
			type = expression.getType();
			break;
		}
		default:
			throw new RuntimeException("Unreachable");
		}
		assert type != null;
		typeNode.setType(type);
		return type;
	}

	/**
	 * <p>
	 * See C11 6.7.2.2 and 6.7.2.3. The procedure is as follows:
	 * </p>
	 * 
	 * <p>
	 * If there is no tag: there has to be an enumerator list, and this defines
	 * a new unnamed entity and enumeration type in the current scope.
	 * </p>
	 * 
	 * <p>
	 * If there is a tag, proceed as follows:
	 * <ul>
	 * <li>
	 * If there is an enumerator list: check that there is no tagged entity with
	 * the same tag in the current scope. If this check fails, syntax error.
	 * Create a new enumeration entity and type, add it to the current scope.</li>
	 * <li>
	 * If there is not an enumerator list: check (1) there is a visible tagged
	 * entity with the same tag; (2) that tagged entity is an enum; and (3) that
	 * previous enum is complete. If any of these fails: syntax error. Else, use
	 * the old entity and type.</li>
	 * </ul>
	 * </p>
	 * 
	 * <p>
	 * Note that the situation is slightly different than that for structures or
	 * unions. An incomplete structure or union declaration may occur before the
	 * structure or union is complete. In contrast, an enumeration must be
	 * complete the first time it is declared, and an incomplete version may
	 * occur only after that point.
	 * </p>
	 * 
	 * @param node
	 * @return
	 * @throws SyntaxException
	 */
	Type processEnumerationType(EnumerationTypeNode node)
			throws SyntaxException {
		Scope scope = node.getScope();
		IdentifierNode identifier = node.getIdentifier(); // could be null
		String tag = node.getName(); // could be null
		SequenceNode<EnumeratorDeclarationNode> enumerators = node
				.enumerators(); // could be null
		EnumerationType enumeration;
		Type result;

		if (node.isRestrictQualified())
			throw error("Use of restrict qualifier with non-pointer type", node);
		if (tag != null) {
			if (enumerators != null) {
				TaggedEntity oldEntity = scope.getTaggedEntity(tag);

				if (oldEntity != null)
					throw error("Re-use of tag " + tag
							+ " for enumeration.  Previous use was at "
							+ oldEntity.getFirstDeclaration().getSource(), node);
				enumeration = createEnumeration(node);
			} else {
				TaggedEntity oldEntity = scope.getLexicalTaggedEntity(tag);

				if (oldEntity == null)
					throw error(
							"See C11 6.7.2.3(3):\n\"A type specifier of the form\n"
									+ "    enum identifier\n"
									+ "without an enumerator list shall only appear after the type\n"
									+ "it specifies is complete.\"", node);
				if (!(oldEntity instanceof EnumerationType))
					throw error(
							"Re-use of tag "
									+ tag
									+ " for enumeration when tag is visible with different kind.  Previous use was at "
									+ oldEntity.getFirstDeclaration()
											.getSource(), node);
				enumeration = (EnumerationType) oldEntity;
				assert enumeration.isComplete();
				// if not, you would have caught the earlier incomplete use
				enumeration.addDeclaration(node);
			}
		} else {
			// no tag: create new anonymous enumeration
			if (enumerators == null)
				throw error("Anonymous enumeration with no enumerator list",
						node);
			enumeration = createEnumeration(node);
		}
		node.setEntity(enumeration);
		if (identifier != null)
			identifier.setEntity(enumeration);
		{
			boolean constQ = node.isConstQualified();
			boolean volatileQ = node.isVolatileQualified();
			UnqualifiedObjectType unqualifiedType = enumeration.getType();

			if (node.isAtomicQualified())
				unqualifiedType = typeFactory.atomicType(unqualifiedType);
			if (constQ || volatileQ)
				result = typeFactory.qualifiedType(unqualifiedType, constQ,
						volatileQ, false, false, false);
			else
				result = unqualifiedType;
		}
		node.setType(result);
		return result;
	}

	/**
	 * <p>
	 * See C11 6.7.2.1 and 6.7.2.3. The procedure is as follows:
	 * </p>
	 * 
	 * <p>
	 * If there is no tag, there has to be a declarator list, and this defines a
	 * new unnamed struct or union entity and type in the current scope. If
	 * there is no declarator list, a syntax exception is thrown.
	 * </p>
	 * 
	 * <p>
	 * If there is a tag, proceed as follows:
	 * <ul>
	 * <li>
	 * If there is a declarator list: see if there exists a tagged entity with
	 * the same tag in current scope.
	 * <ul>
	 * <li>If there does, check it has the same kind (struct or union) as this
	 * one, and check that it is incomplete. If either check fails, throw a
	 * syntax exception. Then complete the old entity using the information from
	 * the given node.</li>
	 * <li>If there does not exist a tagged entity with the same tag in the
	 * current scope, create a new complete struct/union entity and type and add
	 * it to the current scope.</li>
	 * </ul>
	 * </li>
	 * <li>
	 * If there is no declarator list: see if there exists a visible tagged
	 * entity with the same tag. If there does exist such an entity, check it
	 * has the same kind as this one (struct or union), and use it. If there
	 * does not exist such an entity, create a new incomplete struct or union
	 * entity and type and add it to the current scope.</li>
	 * </ul>
	 * </p>
	 * 
	 * @param node
	 *            a structure or union type node
	 * @return the structure or union type obtained by processing the node
	 * @throws SyntaxException
	 *             if any of the consistency checks defined above fails
	 */
	Type processStructureOrUnionType(StructureOrUnionTypeNode node)
			throws SyntaxException {
		Scope scope = node.getScope();
		IdentifierNode identifier = node.getIdentifier(); // could be null
		String tag = node.getName(); // could be null
		SequenceNode<FieldDeclarationNode> fieldDecls = node
				.getStructDeclList(); // could be null
		StructureOrUnionType structureOrUnion;
		Type result;

		if (node.isRestrictQualified())
			throw error("Use of restrict qualifier with non-pointer type", node);
		if (tag == null) {
			if (fieldDecls == null)
				throw error(
						"Anonymous structure or union with no declarator list",
						node);
			structureOrUnion = createStructureOrUnion(node);
		} else {
			if (fieldDecls != null) {
				TaggedEntity oldEntity = scope.getTaggedEntity(tag);

				if (oldEntity != null) {
					checkConsistency(oldEntity, node);
					structureOrUnion = (StructureOrUnionType) oldEntity;
					completeStructOrUnion(structureOrUnion, node);
				} else {
					structureOrUnion = createStructureOrUnion(node);
				}
			} else {
				TaggedEntity oldEntity = scope.getLexicalTaggedEntity(tag);

				if (oldEntity != null) {
					checkConsistency(oldEntity, node);
					structureOrUnion = (StructureOrUnionType) oldEntity;
				} else {
					structureOrUnion = createStructureOrUnion(node);
				}
			}
		}
		structureOrUnion.addDeclaration(node);
		node.setEntity(structureOrUnion);
		if (identifier != null)
			identifier.setEntity(structureOrUnion);
		{
			boolean constQ = node.isConstQualified();
			boolean volatileQ = node.isVolatileQualified();
			UnqualifiedObjectType unqualifiedType = structureOrUnion.getType();

			if (node.isAtomicQualified())
				unqualifiedType = typeFactory.atomicType(unqualifiedType);
			if (constQ || volatileQ)
				result = typeFactory.qualifiedType(unqualifiedType, constQ,
						volatileQ, false, false, false);
			else
				result = unqualifiedType;
		}
		node.setType(result);
		return result;
	}
}
