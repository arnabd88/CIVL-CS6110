package edu.udel.cis.vsl.abc.token.IF;

import java.io.PrintStream;
import java.util.Iterator;

/**
 * A "Source" represents a range of CTokens (post-preprocessor tokens) from the
 * token stream that forms the input to the parser. Typical use: a Source object
 * is associated to each node in an AST to report useful error messages to the
 * user when a syntax error occurs.
 * 
 * @author siegel
 * 
 */
public interface Source {

	/**
	 * Returns the first token in the range of tokens represented by this
	 * Source.
	 * 
	 * @return the first token
	 */
	CivlcToken getFirstToken();

	/**
	 * Returns the last token in the range of tokens represented by this Source.
	 * 
	 * @return the last token
	 */
	CivlcToken getLastToken();

	/**
	 * Returns an iterator over the tokens represented by this Source.
	 * 
	 * @return an iterator over the tokens
	 */
	Iterator<CivlcToken> tokens();

	/**
	 * Returns the number of tokens represented by this Source.
	 * 
	 * @return the number of tokens
	 */
	int getNumTokens();

	/**
	 * Returns a human-readable string representation of this range of source
	 * data.
	 * 
	 * @return user-friendly readable representation
	 */
	String toString();

	void print(PrintStream out);

	/**
	 * Returns location information only (not actual source text). For example
	 * "foo.c:127.4-128.1".
	 * 
	 * @param abbreviated
	 *            true iff want to have the shorter file name, e.g,
	 *            "f1:127.4-128.1" instead of "longOrignialFile.c:127.4-128.1"
	 */
	String getLocation(boolean abbreviated);

	/**
	 * Returns summary of location and text.
	 * 
	 * @param abbreviated
	 *            true iff want to have the shorter file name in the location,
	 *            e.g, "f1:127.4-128.1" instead of
	 *            "longOrignialFile.c:127.4-128.1"
	 * @return summary of location and text
	 */
	String getSummary(boolean abbreviated);

	String getContent(boolean abbreviated);

}
