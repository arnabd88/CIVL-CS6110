package edu.udel.cis.vsl.abc.token.common;

import java.io.PrintStream;
import java.util.Collection;
import java.util.List;

import org.antlr.runtime.Token;

import edu.udel.cis.vsl.abc.token.IF.CivlcToken;
import edu.udel.cis.vsl.abc.token.IF.CivlcTokenSource;
import edu.udel.cis.vsl.abc.token.IF.SourceFile;
import edu.udel.cis.vsl.abc.token.IF.TokenFactory;

public class CommonCivlcTokenSource implements CivlcTokenSource {

	private List<CivlcToken> tokens;
	private TokenFactory tokenFactory;

	public CommonCivlcTokenSource(List<CivlcToken> tokens, TokenFactory factory) {
		this.tokens = tokens;
		this.tokenFactory = factory;
	}

	@Override
	public Token nextToken() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String getSourceName() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public int getNumTokens() {
		return tokens.size() - 1;
	}

	@Override
	public CivlcToken getToken(int index) {
		return this.tokens.get(index);
	}

	@Override
	public TokenFactory getTokenFactory() {
		return this.tokenFactory;
	}

	@Override
	public Collection<SourceFile> getSourceFiles() {
		return null;
	}

	@Override
	public void printShorterFileNameMap(PrintStream out) {
	}

}
