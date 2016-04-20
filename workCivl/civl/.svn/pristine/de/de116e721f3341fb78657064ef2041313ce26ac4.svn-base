package edu.udel.cis.vsl.civl.transform.common;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode.NodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.ExternalDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.token.IF.Formation;
import edu.udel.cis.vsl.abc.token.IF.Macro;
import edu.udel.cis.vsl.abc.token.IF.MacroExpansion;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;

public class MacroTransformer extends CIVLBaseTransformer {

	public final static String CODE = "macro";
	public final static String LONG_NAME = "MacroTransformer";
	public final static String SHORT_DESCRIPTION = "recovers macros from C programs to CIVL-C";

	public MacroTransformer(ASTFactory astFactory) {
		super(CODE, LONG_NAME, SHORT_DESCRIPTION, astFactory);
	}

	@Override
	public AST transform(AST unit) throws SyntaxException {
		SequenceNode<ExternalDefinitionNode> root = unit.getRootNode();
		AST newAst;
		List<ExternalDefinitionNode> newExternalList = new ArrayList<>();
		Map<String, VariableDeclarationNode> macroVars = new HashMap<>();

		unit.release();
		for (ASTNode child : root) {
			if (child != null)
				recoverMacro(child, macroVars);
		}
		for (ExternalDefinitionNode inputVar : macroVars.values())
			newExternalList.add(inputVar);
		for (ExternalDefinitionNode child : root) {
			if (child != null) {
				newExternalList.add(child);
				child.parent().removeChild(child.childIndex());
			}
		}
		root = nodeFactory.newSequenceNode(root.getSource(), "TranslationUnit",
				newExternalList);
		newAst = astFactory.newAST(root);
		return newAst;
	}

	private void recoverMacro(ASTNode node,
			Map<String, VariableDeclarationNode> macros) {
		String sourceFile = node.getSource().getFirstToken().getSourceFile()
				.getName();
		Formation formation;

		if (sourceFile.endsWith(".h") || sourceFile.endsWith(".cvh")
				|| sourceFile.equals("civl-omp.cvl")
				|| sourceFile.equals("mpi.cvl")
				|| sourceFile.equals("pthread-c.cvl")
				|| sourceFile.equals("pthread.cvl")
				|| sourceFile.equals("stdio-c.cvl")
				|| sourceFile.equals("stdio.cvl"))
			return;
		formation = node.getSource().getFirstToken().getFormation();
		if (formation instanceof MacroExpansion) {
			if (node.nodeKind() == NodeKind.EXPRESSION) {
				Type type = ((ExpressionNode) node).getType();

				if (type instanceof StandardBasicType) {
					if (((StandardBasicType) type).getBasicTypeKind() == BasicTypeKind.BOOL)
						return;
				}
				MacroExpansion expansion = (MacroExpansion) formation;
				Macro macro = expansion.getMacro();
				String name = macro.getName();
				ExpressionNode idNode;
				Source source = node.getSource();

				if (!macros.containsKey(name)) {
					VariableDeclarationNode newInputVar;
					TypeNode typeNode = typeNode(source, type);

					typeNode.setInputQualified(true);
					newInputVar = nodeFactory.newVariableDeclarationNode(
							source,
							nodeFactory.newIdentifierNode(source, name),
							typeNode);
					macros.put(name, newInputVar);
				}
				idNode = this.identifierExpression(source, name);
				node.parent().setChild(node.childIndex(), idNode);
			}
		} else {
			for (ASTNode child : node.children()) {
				if (child != null) {
					this.recoverMacro(child, macros);
				}
			}
		}
	}
}
