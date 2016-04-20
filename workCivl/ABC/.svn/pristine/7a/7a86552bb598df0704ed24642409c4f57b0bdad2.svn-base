package edu.udel.cis.vsl.abc.front.c.astgen;

import java.util.List;

import org.antlr.runtime.ANTLRStringStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.Token;
import org.antlr.runtime.tree.CommonTree;

import edu.udel.cis.vsl.abc.ast.node.IF.NodeFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.ContractNode;
import edu.udel.cis.vsl.abc.config.IF.Configurations.Language;
import edu.udel.cis.vsl.abc.err.IF.ABCRuntimeException;
import edu.udel.cis.vsl.abc.front.c.parse.AcslParser;
import edu.udel.cis.vsl.abc.front.c.parse.CParser.RuleKind;
import edu.udel.cis.vsl.abc.front.c.preproc.AcslLexer;
import edu.udel.cis.vsl.abc.front.c.ptree.CParseTree;
import edu.udel.cis.vsl.abc.front.common.astgen.SimpleScope;
import edu.udel.cis.vsl.abc.token.IF.Formation;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.token.IF.TokenFactory;

public class AcslContractHandler {

	public enum AcslContractKind {
		FUNCTION_CONTRACT, LOOP_CONTRACT
	}

	private NodeFactory nodeFactory;
	private TokenFactory tokenFactory;

	public AcslContractHandler(NodeFactory factory, TokenFactory tokenFactory) {
		this.nodeFactory = factory;
		this.tokenFactory = tokenFactory;
	}

	public List<ContractNode> translateContracts(int startLine, String text,
			SimpleScope scope, Formation formation, AcslContractKind kind)
			throws SyntaxException {
		CParseTree contractTree = this.parse(startLine, text, formation, kind);
		AcslContractWorker worker = new AcslContractWorker(nodeFactory,
				tokenFactory, contractTree);

		return worker.generateASTNodes(scope);
	}

	private CParseTree parse(int startLine, String text, Formation formation,
			AcslContractKind kind) throws SyntaxException {
		ANTLRStringStream input = new ANTLRStringStream(text);
		AcslLexer lexer = new AcslLexer(input);
		CommonTokenStream tokens = new CommonTokenStream(lexer);
		AcslParser parser = new AcslParser(tokens);
		CommonTree tree;

		updateLineNumber(startLine - 1, tokens);
		try {
			switch (kind) {
			case FUNCTION_CONTRACT:
				tree = (CommonTree) parser.function_contract().getTree();
				break;
			case LOOP_CONTRACT:
				tree = (CommonTree) parser.loop_contract().getTree();
				break;
			default:
				throw new SyntaxException(
						"unknown ACSL contract kind: " + kind, null);
			}
		} catch (RecognitionException e) {
			throw new ABCRuntimeException(e.getMessage());
		}
		// System.out.print(tree);
		// generateASTNodes(tree);

		return new CParseTree(Language.CIVL_C, RuleKind.CONTRACT,
				this.tokenFactory.getCivlcTokenSourceByTokens(
						tokens.getTokens(), formation), tree);
	}

	private void updateLineNumber(int offset, CommonTokenStream tokens) {
		for (Token token : tokens.getTokens()) {
			token.setLine(token.getLine() + offset);
		}
	}
}
