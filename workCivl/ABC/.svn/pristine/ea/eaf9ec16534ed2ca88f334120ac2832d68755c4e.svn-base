package edu.udel.cis.vsl.abc.analysis.IF;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;

/**
 * An analyzer is an object which performs some kind of analysis on an AST,
 * typically leaving behind the information in the AST.
 * 
 * @author siegel
 * 
 */
public interface Analyzer {

	/**
	 * Performs the analysis on the given AST.
	 * 
	 * @param ast
	 *            the AST
	 * @throws SyntaxException
	 *             if some kind of defect is found in the AST
	 */
	void analyze(AST ast) throws SyntaxException;

	/**
	 * Removes all analysis artifacts added to the AST by the
	 * {@link #analyze(AST)} method.
	 * 
	 * @param ast
	 *            the AST
	 */
	void clear(AST ast);

}
