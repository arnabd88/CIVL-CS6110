package edu.udel.cis.vsl.civl.transform.common;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.udel.cis.vsl.abc.antlr2ast.IF.ASTBuilder;
import edu.udel.cis.vsl.abc.antlr2ast.IF.Antlr2AST;
import edu.udel.cis.vsl.abc.antlr2ast.IF.CIVLPragmaBuilder;
import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode.NodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.PragmaNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CompoundStatementNode;
import edu.udel.cis.vsl.abc.parse.IF.ParseException;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;

public class CIVLPragmaTransformer extends CIVLBaseTransformer {

	public final static String CODE = "civlc";
	public final static String LONG_NAME = "CIVL Pragma Transformer";
	public final static String SHORT_DESCRIPTION = "parse CIVL pragmas into AST nodes";

	public final static String CIVL = "CIVL";
	public final static String INPUT = "$input";

	private CIVLPragmaBuilder civlBuilder;

	// private ASTNode rootNode;

	public CIVLPragmaTransformer(ASTFactory astFactory, ASTBuilder astBuilder,
			CIVLConfiguration config) {
		super(CODE, LONG_NAME, SHORT_DESCRIPTION, astFactory, astBuilder,
				config);
		this.civlBuilder = Antlr2AST.newCIVLPragmaBuilder(astBuilder);
	}

	@Override
	public AST transform(AST ast) throws SyntaxException {
		ASTNode root = ast.getRootNode();

		ast.release();
		try {
			this.processASTNode(root);
		} catch (ParseException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return astFactory.newAST(root);
	}

	private void processASTNode(ASTNode node) throws SyntaxException,
			ParseException {
		Map<String, VariableDeclarationNode> civlPragmaVariables = new HashMap<>();

		if (node.nodeKind() == NodeKind.PRAGMA) {
			PragmaNode pragma = (PragmaNode) node;

			if (pragma.getPragmaIdentifier().name().equals(CIVL)) {
				// TODO translates CIVL pragma
				processPragmaNode(pragma, civlPragmaVariables);

			}
			// } else if (node instanceof VariableDeclarationNode) {
			// VariableDeclarationNode variable = (VariableDeclarationNode)
			// node;
			// String name = variable.getIdentifier().name();
			//
			// if (civlPragmaVariables.containsKey(name))
			// variable.parent().setChild(variable.childIndex(),
			// civlPragmaVariables.get(name));
		} else {
			for (ASTNode child : node.children()) {
				if (child != null)
					processASTNode(child);
			}
		}
	}

	void processPragmaNode(PragmaNode pragma,
			Map<String, VariableDeclarationNode> civlPragmaVariables)
			throws SyntaxException, ParseException {
		List<BlockItemNode> result = civlBuilder.getBlockItem(pragma
				.getTokens());

		if (result.size() == 1) {
			pragma.parent().setChild(pragma.childIndex(), result.get(0));
		} else {
			CompoundStatementNode compound = nodeFactory
					.newCompoundStatementNode(pragma.getSource(), result);

			pragma.parent().setChild(pragma.childIndex(), compound);
		}
	}
}
