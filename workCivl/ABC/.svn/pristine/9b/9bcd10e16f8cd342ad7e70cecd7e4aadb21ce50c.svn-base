package edu.udel.cis.vsl.abc.token.IF;

import org.antlr.runtime.TokenStream;

/**
 * <p>
 * Represents a finite sequence of {@link CivlcToken}. Methods are provided to
 * access the sequence in a variety of convenient ways. Most importantly, method
 * {@link #newSource()} returns a {@link CivlcTokenSource}, which can be used to
 * construct an ANTLR {@link TokenStream}, which can in turn be used as the
 * input to an ANTLR parser.
 * </p>
 * 
 * <p>
 * The tokens are never duplicated by any of these methods, so a modification to
 * a token will be reflected in any subsequence method calls to access that
 * token.
 * </p>
 * 
 * <p>
 * This sequence representation is best use for relatively short sequences, such
 * as the tokens comprising a single pragma. It is not recommended for
 * representing an entire translation unit.
 * </p>
 * 
 * <p>
 * This object will also include an addition "EOF" token. That token is not part
 * of the sequence, but it is used by method {@link #newSource()}. That method
 * will in effect append an infinite sequence of EOF tokens to the end of the
 * sequence.
 * </p>
 * 
 * @author siegel
 * 
 */
public interface CivlcTokenSequence {

	/**
	 * Returns the extra EOF token which is used by method {@link #newSource()}.
	 * 
	 * @return the extra EOF token
	 */
	CivlcToken getEOFToken();

	/**
	 * <p>
	 * Returns a new {@link CivlcTokenSource} which produces the tokens in this
	 * sequence, in order, with an "EOF" token appended. Since a token source is
	 * basically infinite, the final EOF token is stuttered, i.e., repeated
	 * calls to {@link CivlcTokenSource#nextToken()} will continue to produce the
	 * EOF token after the EOF token has been reached.
	 * </p>
	 * 
	 * <p>
	 * This source may be used to construct a {@link TokenStream} and then used
	 * as the input to a parser.
	 * </p>
	 * 
	 * @return a new {@link CivlcTokenSource} yielding the elements of this
	 *         sequence.
	 */
	CivlcTokenSource newSource();

	/**
	 * Returns the tokens as an array. Whether or not this array can be modified
	 * depends on the implementation. The array does not include the extra "EOF"
	 * token. The length of this array is the same as the number returned by
	 * {@link #size()}.
	 * 
	 * @return the tokens as an array
	 */
	CivlcToken[] getTokens();

	/**
	 * Returns the number of tokens in the sequence. This number does not
	 * include the extra "EOF" token.
	 * 
	 * @return the number of tokens in the sequence
	 */
	int size();
}
