package edu.udel.cis.vsl.abc.transform.common;

import java.util.LinkedHashMap;
import java.util.Map;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.entity.IF.Entity;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode.NodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.transform.IF.BaseTransformer;
import edu.udel.cis.vsl.abc.transform.IF.NameTransformer;

/**
 * Transform an AST by modifying the names of entities.
 * 
 * @author zirkel
 * 
 */
public class CommonNameTransformer extends BaseTransformer implements
		NameTransformer {

	public final static String CODE = "name";
	public final static String LONG_NAME = "NameTransformer";
	public final static String SHORT_DESCRIPTION = "renames references to entities";

	/** The map from entities to their new names. */
	private Map<Entity, String> nameChanges;

	/** Map from identifier nodes to their new names. */
	private Map<IdentifierNode, String> identifierNameMap;

	public CommonNameTransformer(Map<Entity, String> nameChanges,
			ASTFactory factory) {
		super(CODE, LONG_NAME, SHORT_DESCRIPTION, factory);
		this.nameChanges = nameChanges;
	}

	@Override
	public AST transform(AST unit) throws SyntaxException {
		SequenceNode<BlockItemNode> rootNode = unit.getRootNode();
		AST result;

		identifierNameMap = new LinkedHashMap<IdentifierNode, String>();
		astFactory = unit.getASTFactory();
		findIdentifiers(rootNode);
		unit.release();
		for (IdentifierNode identifierNode : identifierNameMap.keySet()) {
			identifierNode.setName(identifierNameMap.get(identifierNode));
		}
		result = astFactory.newAST(rootNode, unit.getSourceFiles(),
				unit.isWholeProgram());
		return result;
	}

	private void findIdentifiers(ASTNode node) {
		if (node == null) {
			return;
		}
		if (node.nodeKind() == NodeKind.IDENTIFIER) {
			Entity identifierEntity = ((IdentifierNode) node).getEntity();

			if (nameChanges.containsKey(identifierEntity)) {
				identifierNameMap.put((IdentifierNode) node,
						nameChanges.get(identifierEntity));
			}
		} else {
			for (int i = 0; i < node.numChildren(); i++) {
				findIdentifiers(node.child(i));
			}
		}
	}

}
