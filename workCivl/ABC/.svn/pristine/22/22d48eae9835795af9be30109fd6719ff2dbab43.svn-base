package edu.udel.cis.vsl.abc.token.common;

import java.io.PrintStream;
import java.util.Collection;

import org.antlr.runtime.Token;

import edu.udel.cis.vsl.abc.front.IF.CivlcTokenConstant;
import edu.udel.cis.vsl.abc.token.IF.CivlcToken;
import edu.udel.cis.vsl.abc.token.IF.CivlcTokenSequence;
import edu.udel.cis.vsl.abc.token.IF.CivlcTokenSource;
import edu.udel.cis.vsl.abc.token.IF.SourceFile;
import edu.udel.cis.vsl.abc.token.IF.TokenFactory;

public class CivlcTokenSubSequence implements CivlcTokenSequence {

	int startTokenIndex;

	int lastTokenIndex;

	CivlcTokenSource rootSource;

	CivlcToken eofToken;

	/**
	 * A helper class which represents a subsequence of sequence of tokens
	 * through the CTokenSource abstraction.
	 * 
	 * @author siegel
	 * 
	 */
	class SubTokenSource implements CivlcTokenSource {

		int currentTokenIndex = startTokenIndex;

		@Override
		public Token nextToken() {
			if (currentTokenIndex > lastTokenIndex) {
				return eofToken;
			} else {
				Token result = rootSource.getToken(currentTokenIndex);

				currentTokenIndex++;
				return result;
			}
		}

		@Override
		public String getSourceName() {
			return rootSource.getSourceName();
		}

		@Override
		public int getNumTokens() {
			return currentTokenIndex - startTokenIndex;
		}

		@Override
		public CivlcToken getToken(int index) {
			return rootSource.getToken(index);
		}

		@Override
		public TokenFactory getTokenFactory() {
			return rootSource.getTokenFactory();
		}

		@Override
		public void printShorterFileNameMap(PrintStream out) {
			rootSource.printShorterFileNameMap(out);
		}

		@Override
		public Collection<SourceFile> getSourceFiles() {
			return rootSource.getSourceFiles();
		}
	}

	public CivlcTokenSubSequence(CivlcTokenSource rootSource, int startTokenIndex,
			int lastTokenIndex) {
		this.rootSource = rootSource;
		this.startTokenIndex = startTokenIndex;
		this.lastTokenIndex = lastTokenIndex;
		this.eofToken = rootSource.getTokenFactory().newCivlcToken(
				CivlcTokenConstant.EOF, "EOF", null);
	}

	@Override
	public CivlcTokenSource newSource() {
		return new SubTokenSource();
	}

	@Override
	public CivlcToken[] getTokens() {
		int numTokens = size();
		CivlcToken[] result = new CivlcToken[numTokens];

		for (int i = 0; i < numTokens; i++) {
			result[i] = rootSource.getToken(startTokenIndex + i);
		}
		return result;
	}

	@Override
	public int size() {
		return lastTokenIndex - startTokenIndex + 1;
	}

	@Override
	public CivlcToken getEOFToken() {
		return this.eofToken;
	}
}
