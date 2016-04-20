package edu.udel.cis.vsl.abc.token.IF;

import org.antlr.runtime.Token;

/**
 * A FunctionMacro represents a C preprocessor function-like macro, which has
 * the from <code>#define f(X1,X2,...) ...</code>. The name of the macro is
 * <code>f</code>, the <code>X1</code>,<code>X2</code>, etc., are the formal
 * parameters, and the <code>...</code> is a sequence of replacement tokens. The
 * replacement tokens may include the formal parameters.
 * 
 * @author siegel
 * 
 */
public interface FunctionMacro extends Macro {

	/**
	 * Returns the number of formal parameters
	 * 
	 * @return the number of formal parameters
	 */
	int getNumFormals();

	/**
	 * Gets the index-th formal parmamter
	 * 
	 * @param index
	 *            an integer in the range [0,numFormals-1]
	 * @return the index-th formal parameter token
	 */
	Token getFormal(int index);

	/**
	 * Given i, 0<=i<n, where n is the number of replacement tokens, let t be
	 * the i-th replacement token. Returns -1 if t is not an identifier equal to
	 * one of the formal parameter identifiers. Otherwise, returns the index of
	 * that formal parameter. This is to faciliate substitution of actuals for
	 * formals.
	 * 
	 * @param i
	 *            integer in [0,numReplacementTokens)
	 * @return -1 or index of matching formal parameter in [0,numFormals)
	 */
	int getReplacementFormalIndex(int i);

}
