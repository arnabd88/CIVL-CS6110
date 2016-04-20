package edu.udel.cis.vsl.abc.ast.node.IF;

import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.token.IF.CivlcToken;
import edu.udel.cis.vsl.abc.token.IF.CivlcTokenSource;

/**
 * A pragma may be included in the AST wherever a statement or an external
 * definition may occur. The pragma is represented as an identifier (the first
 * token to follow the <code># pragma</code> tokens), followed by some sequence
 * of tokens of length (say) n, followed by a newline character. We will refer
 * to that sequence as the "pragma body". Note that the pragma body does not
 * include the pragma identifier and does not include the final newline
 * character.
 * 
 * @author siegel
 * 
 */
public interface PragmaNode extends StatementNode {

	/**
	 * Returns the pragma identifier, i.e., the identifier immediately following
	 * <code># pragma</code>. For example, in <code># pragma omp ...</code>, the
	 * identifier <code>omp</code> would be returned.
	 * 
	 * @return the pragma identifier
	 */
	IdentifierNode getPragmaIdentifier();

	/**
	 * Returns n, the number of tokens in the pragma body, i.e., the number of
	 * tokens following <code># pragma IDENTIFIER</code>
	 * 
	 * @return number of tokens in the pragma body
	 */
	int getNumTokens();

	/**
	 * Returns the index-th token in the pragma body. The tokens of body are
	 * indexed beginning with 0.
	 * 
	 * @param index
	 *            an integer in the range [0,n-1], where n is the value returned
	 *            by {@link #getNumTokens}
	 * 
	 * @return the index-th token in the pragma body
	 */
	CivlcToken getToken(int index);

	/**
	 * Returns an iterable over the tokens in the pragma body.
	 * 
	 * @return iterator over the tokens of pragma body
	 */
	Iterable<CivlcToken> getTokens();

	/**
	 * <p>
	 * Returns the tokens of the pragma body as a {@link CivlcTokenSource}, which
	 * can then be fed into an ANTLR parser for syntactic analysis. Note that
	 * each call returns a new token source, since each can only be used once.
	 * </p>
	 * 
	 * <p>
	 * The token source will effectively append an infinite sequence of EOF
	 * tokens after the pragma body. This is what is expected from most parsers.
	 * </p>
	 * 
	 * @return a token source for the tokens comprising the body of this pragma
	 */
	CivlcTokenSource newTokenSource();

	/**
	 * Returns the newline token which terminates this pragma.
	 * 
	 * @return the newline token
	 */
	CivlcToken getNewlineToken();

	@Override
	PragmaNode copy();
}
