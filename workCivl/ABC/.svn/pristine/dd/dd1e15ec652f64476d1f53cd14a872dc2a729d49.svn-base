package edu.udel.cis.vsl.abc.front.common.ptree;

import java.util.Collection;

import org.antlr.runtime.tree.CommonTree;

import edu.udel.cis.vsl.abc.config.IF.Configurations.Language;
import edu.udel.cis.vsl.abc.front.IF.ParseTree;
import edu.udel.cis.vsl.abc.token.IF.CivlcToken;
import edu.udel.cis.vsl.abc.token.IF.CivlcTokenSequence;
import edu.udel.cis.vsl.abc.token.IF.CivlcTokenSource;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SourceFile;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.token.IF.TokenFactory;

public abstract class CommonParseTree implements ParseTree {

	protected Language language;

	protected CivlcTokenSource tokenSource;

	protected TokenFactory tokenFactory;

	protected CommonTree root;

	public CommonParseTree(Language language, CivlcTokenSource tokenSource,
			CommonTree root) {
		this.language = language;
		this.tokenSource = tokenSource;
		this.tokenFactory = tokenSource.getTokenFactory();
		this.root = root;
	}

	@Override
	public Language getLanguage() {
		return this.language;
	}

	@Override
	public CommonTree getRoot() {
		return root;
	}

	@Override
	public Source source(CommonTree tree) {
		CivlcToken firstToken = null, lastToken = null;
		int start = tree.getTokenStartIndex();
		int stop = tree.getTokenStopIndex();

		if (start >= 0)
			firstToken = tokenSource.getToken(start);
		if (stop >= 0)
			lastToken = tokenSource.getToken(stop);
		if (firstToken == null)
			if (lastToken == null)
				throw new IllegalArgumentException(
						"No tokens associated to tree node " + tree);
			else
				firstToken = lastToken;
		else if (lastToken == null)
			lastToken = firstToken;
		return tokenFactory.newSource(firstToken, lastToken);
	}

	@Override
	public SyntaxException newSyntaxException(String message, CommonTree tree) {
		return tokenFactory.newSyntaxException(message, source(tree));
	}

	@Override
	public CivlcTokenSequence getTokenSourceProducer(CommonTree tokenListNode) {
		int numChildren = tokenListNode.getChildCount();

		if (numChildren == 0) {
			return tokenFactory.getEmptyTokenSubsequence(tokenSource);
		} else {
			CivlcToken startToken = (CivlcToken) ((CommonTree) tokenListNode
					.getChild(0)).getToken();
			CivlcToken stopToken = (CivlcToken) ((CommonTree) tokenListNode
					.getChild(numChildren - 1)).getToken();

			return tokenFactory.getTokenSubsequence(tokenSource, startToken,
					stopToken);
		}
	}

	@Override
	public Collection<SourceFile> getSourceFiles() {
		return tokenSource.getSourceFiles();
	}

	@Override
	public String toString() {
		return tokenSource.toString();
	}

	@Override
	public CivlcTokenSource getCivlcTokenSource() {
		return this.tokenSource;
	}

	@Override
	public TokenFactory getTokenFactory() {
		return this.tokenFactory;
	}
}
