package edu.udel.cis.vsl.civl.transform.common;

import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode.NodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.ast.type.IF.ArrayType;
import edu.udel.cis.vsl.abc.ast.type.IF.PointerType;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.transform.IF.BaseTransformer;

/**
 * This is the base transformer of CIVL. Any transformer implemented in CIVL
 * should extend this class. This class extends BaseTransformer (from ABC) and
 * provides extra instance fields and common methods to be used by any
 * particular transformers.
 * 
 * @author Manchun Zheng
 * 
 */
public abstract class CIVLBaseTransformer extends BaseTransformer {

	/* ****************************** Constructor ************************** */

	/**
	 * Creates a new instance of CIVLBaseTransformer.
	 * 
	 * @param code
	 *            The code of the transformer.
	 * @param longName
	 *            The full name of the transformer.
	 * @param shortDescription
	 *            The description of the transformer.
	 * @param astFactory
	 *            The ASTFactory that will be used to create new AST nodes.
	 * 
	 */
	protected CIVLBaseTransformer(String code, String longName,
			String shortDescription, ASTFactory astFactory) {
		super(code, longName, shortDescription, astFactory);
	}

	/* ************************** Protected Methods ************************ */

	/**
	 * Creates an identifier expression node with a given name.
	 * 
	 * @param source
	 *            The source information of the identifier.
	 * @param name
	 *            The name of the identifier.
	 * @return
	 */
	protected ExpressionNode identifierExpression(Source source, String name) {
		return nodeFactory.newIdentifierExpressionNode(source,
				nodeFactory.newIdentifierNode(source, name));
	}

	/* *************************** Public Methods ************************* */

	protected Source getMainSource(ASTNode node) {
		if (node.nodeKind() == NodeKind.FUNCTION_DEFINITION) {
			FunctionDefinitionNode functionNode = (FunctionDefinitionNode) node;
			IdentifierNode functionName = (IdentifierNode) functionNode
					.child(0);

			if (functionName.name().equals("main")) {
				return node.getSource();
			}
		}
		for (ASTNode child : node.children()) {
			if (child == null)
				continue;
			else {
				Source childResult = getMainSource(child);

				if (childResult != null)
					return childResult;
			}
		}
		return null;
	}

	protected VariableDeclarationNode variableDeclaration(Source source,
			String name, TypeNode type) {
		return nodeFactory.newVariableDeclarationNode(source,
				nodeFactory.newIdentifierNode(source, name), type);
	}

	protected VariableDeclarationNode variableDeclaration(Source source,
			String name, TypeNode type, ExpressionNode init) {
		return nodeFactory.newVariableDeclarationNode(source,
				nodeFactory.newIdentifierNode(source, name), type, init);
	}

	protected TypeNode typeNode(Source source, Type type) {
		switch (type.kind()) {
		case VOID:
			return nodeFactory.newVoidTypeNode(source);
		case BASIC:
			return nodeFactory.newBasicTypeNode(source,
					((StandardBasicType) type).getBasicTypeKind());
		case OTHER_INTEGER:
			return nodeFactory.newBasicTypeNode(source, BasicTypeKind.INT);
		case ARRAY:
			return nodeFactory.newArrayTypeNode(source,
					this.typeNode(source, ((ArrayType) type).getElementType()),
					((ArrayType) type).getVariableSize().copy());
		case POINTER:
			return nodeFactory.newPointerTypeNode(source, this.typeNode(source,
					((PointerType) type).referencedType()));
		default:
		}
		return null;
	}

}
