package edu.udel.cis.vsl.abc.token.common;

import java.io.PrintStream;
import java.util.Iterator;

import edu.udel.cis.vsl.abc.token.IF.CivlcToken;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.TokenUtils;

public class CommonSource implements Source {

	private CivlcToken firstToken;

	private CivlcToken lastToken;

	public CommonSource(CivlcToken firstToken, CivlcToken lastToken) {
		if (firstToken == null)
			throw new IllegalArgumentException("Null firstToken");
		if (lastToken == null)
			throw new IllegalArgumentException("Null lastToken");

		int first = firstToken.getIndex();
		int last = lastToken.getIndex();

		if (last < first)
			throw new IllegalArgumentException("Last token precedes first:\n"
					+ firstToken + "\n" + lastToken);
		this.firstToken = firstToken;
		this.lastToken = lastToken;
	}

	@Override
	public CivlcToken getFirstToken() {
		return firstToken;
	}

	@Override
	public CivlcToken getLastToken() {
		return lastToken;
	}

	@Override
	public Iterator<CivlcToken> tokens() {
		return new SourceTokenIterator(firstToken, lastToken);
	}

	@Override
	public int getNumTokens() {
		return lastToken.getIndex() - firstToken.getIndex() + 1;
	}

	@Override
	public String toString() {
		return getSummary(false);
	}

	@Override
	public void print(PrintStream out) {
		out.print(getSummary(false));
	}

	@Override
	public String getLocation(boolean abbreviated) {
		return TokenUtils.summarizeRangeLocation(firstToken, lastToken,
				abbreviated);
	}

	@Override
	public String getSummary(boolean abbreviated) {
		return TokenUtils.summarizeRange(firstToken, lastToken, abbreviated);
	}

	@Override
	public String getContent(boolean abbreviated) {
		return TokenUtils.contentOfRange(firstToken, lastToken, abbreviated);
	}
}

class SourceTokenIterator implements Iterator<CivlcToken> {
	CivlcToken nextToken;
	CivlcToken last;

	SourceTokenIterator(CivlcToken firstToken, CivlcToken lastToken) {
		nextToken = firstToken;
		last = lastToken;
	}

	public CivlcToken next() {
		CivlcToken result = nextToken;

		if (nextToken == last)
			nextToken = null;
		else
			nextToken = nextToken.getNext();
		return result;
	}

	public boolean hasNext() {
		return nextToken != null;
	}

	@Override
	public void remove() {
		throw new UnsupportedOperationException();
	}
}
