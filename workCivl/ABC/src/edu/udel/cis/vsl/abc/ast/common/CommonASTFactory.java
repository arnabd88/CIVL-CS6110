package edu.udel.cis.vsl.abc.ast.common;

import java.util.Collection;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.NodeFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.type.IF.TypeFactory;
import edu.udel.cis.vsl.abc.token.IF.SourceFile;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.token.IF.TokenFactory;

//TODO improve the printing of variable declarations when array type is involved.

public class CommonASTFactory implements ASTFactory {

	private NodeFactory nodeFactory;

	private TokenFactory tokenFactory;

	private TypeFactory typeFactory;

	public CommonASTFactory(NodeFactory nodeFactory, TokenFactory tokenFactory,
			TypeFactory typeFactory) {
		this.nodeFactory = nodeFactory;
		this.tokenFactory = tokenFactory;
		this.typeFactory = typeFactory;
	}

	@Override
	public NodeFactory getNodeFactory() {
		return nodeFactory;
	}

	@Override
	public TokenFactory getTokenFactory() {
		return tokenFactory;
	}

	@Override
	public TypeFactory getTypeFactory() {
		return typeFactory;
	}

	@Override
	public AST newAST(SequenceNode<BlockItemNode> root,
			Collection<SourceFile> sourceFiles, boolean isWholeprogram)
			throws SyntaxException {
		AST unit = new CommonAST(this, root, false, sourceFiles, isWholeprogram);

		// do some preparation?
		return unit;
	}
}
