package edu.udel.cis.vsl.abc.front.common.preproc;

import java.util.Iterator;

import edu.udel.cis.vsl.abc.token.IF.CivlcToken;

/**
 * A simple iterator over CTokens that works by following the "next" fields in
 * the tokens.
 * 
 * @author Stephen F. Siegel, University of Delaware
 * 
 */
public class CTokenIterator implements Iterator<CivlcToken> {

	private CivlcToken theNextToken;

	public CTokenIterator(CivlcToken firstToken) {
		theNextToken = firstToken;
	}

	@Override
	public boolean hasNext() {
		return theNextToken != null;
	}

	@Override
	public CivlcToken next() {
		CivlcToken result = theNextToken;

		theNextToken = theNextToken.getNext();
		return result;
	}

	@Override
	public void remove() {
		throw new UnsupportedOperationException("Should not happen");
	}

}
