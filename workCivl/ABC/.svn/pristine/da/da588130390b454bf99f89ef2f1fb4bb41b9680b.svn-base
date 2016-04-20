package edu.udel.cis.vsl.abc.token.IF;

import org.antlr.runtime.Token;

/**
 * A MacroExpansion represents an instance of the expansion of a preprocessor
 * (object or function) macro, which replaces one token by a sequence of new
 * tokens. This object represents the result of a macro expansion as it relates
 * to two tokens: the original (or "start") token before substitution, and the
 * resulting replacement token.
 * 
 * @author siegel
 * 
 */
public interface MacroExpansion extends Formation {

	/**
	 * Gets the original token which was replaced. For an object macro, there is
	 * only one such possible token in each instance of macro expansion; it is
	 * the token which is an identifier with the name of the macro. For a
	 * function macro, it is one of the tokens in one of the arguments to the
	 * macro or the function macro identifier itself.
	 * 
	 * @return the original token which is replaced
	 */
	CivlcToken getStartToken();

	/**
	 * Returns the (function or object) macro that is being applied.
	 * 
	 * @return the macro being applied
	 */
	Macro getMacro();

	/**
	 * Returns the index of the replacement token in the sequence of replacement
	 * tokens specified in the macro definition.
	 * 
	 * @return the replacement token index
	 */
	int getReplacementTokenIndex();

	/**
	 * Returns the replacement token that was substituted for the original start
	 * token.
	 * 
	 * @return the replacement token
	 */
	Token getReplacementToken();

}
