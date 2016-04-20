package edu.udel.cis.vsl.abc.front.c.astgen;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.config.IF.Configuration;
import edu.udel.cis.vsl.abc.front.IF.ASTBuilder;
import edu.udel.cis.vsl.abc.front.IF.ParseTree;
import edu.udel.cis.vsl.abc.front.c.ptree.CParseTree;
import edu.udel.cis.vsl.abc.front.common.astgen.ASTBuilderWorker;
import edu.udel.cis.vsl.abc.front.common.astgen.PragmaFactory;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;

public class CASTBuilder implements ASTBuilder {

	private ASTFactory astFactory;

	private PragmaFactory pragmaFactory;

	private Configuration config;

	public CASTBuilder(Configuration config, ASTFactory astFactory) {
		this.astFactory = astFactory;
		this.config = config;
		pragmaFactory = new PragmaFactory(this);
	}

	@Override
	public AST getTranslationUnit(ParseTree tree) throws SyntaxException {
		ASTBuilderWorker worker = getWorker(tree);
		SequenceNode<BlockItemNode> rootNode = worker.translateRoot();
		AST ast = astFactory.newAST(rootNode,
				((CParseTree) tree).getSourceFiles(), false);

		return ast;
	}

	public CASTBuilderWorker getWorker(ParseTree tree) {
		return new CASTBuilderWorker(config, (CParseTree) tree, astFactory,
				pragmaFactory);
	}

	@Override
	public ASTFactory getASTFactory() {
		return astFactory;
	}

	@Override
	public PragmaFactory getPragmaFactory() {
		return pragmaFactory;
	}
}
