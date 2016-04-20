package edu.udel.cis.vsl.abc.token.IF;

import java.io.PrintStream;
import java.util.Collection;

import org.antlr.runtime.TokenSource;

/**
 * <p>
 * Extends ANTLR's {@link TokenSource} interface by adding some additional
 * functionality: getting the macro information, and methods to get the number
 * of tokens produced so far and to retrieve any token produced so far by index.
 * </p>
 * 
 * <p>
 * Here are the methods specified in ANTLR's TokenSource interface:
 * 
 * <pre>
 * * Return a Token object from your input stream (usually a CharStream).
 * * Do not fail/return upon lexing error; keep chewing on the characters
 * * until you get a good one; errors are not passed through to the parser.
 * 	public Token nextToken();
 * 
 *  * Where are you getting tokens from? normally the implication will simply
 *  * ask lexers input stream.
 * 	public String getSourceName();
 * </pre>
 * 
 * </p>
 * 
 * @author siegel
 * 
 */
public interface CivlcTokenSource extends TokenSource {

	/**
	 * The number of tokens produced by this token source so far.
	 * 
	 * @return number of tokens produced at this time
	 */
	int getNumTokens();

	/**
	 * Returns the index-th token produced (indexed from 0).
	 * 
	 * @param index
	 *            an integer in the range [0,numTokens-1]
	 * @return the index-th token produced
	 */
	CivlcToken getToken(int index);

	/**
	 * Returns the token factory used by this token source object.
	 * 
	 * @return the token factory used by this token source object
	 */
	TokenFactory getTokenFactory();

	/**
	 * Returns the set of source files that were used to create this token
	 * source.
	 * 
	 * @return the set of source files
	 */
	Collection<SourceFile> getSourceFiles();

	void printShorterFileNameMap(PrintStream out);

}
