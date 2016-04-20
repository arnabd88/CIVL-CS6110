package edu.udel.cis.vsl.abc.token.IF;

/**
 * A string literal object results from processing a string literal in the
 * source code. It consists of a sequence of execution characters. The execution
 * charcters are obtained by interpreting the source characters in the source
 * literal. Multiple source characters may encode a single execution character,
 * using escape sequences and unicode encodings.
 * 
 * The C11 Standard also specifies various kinds of strings, distinguished by
 * the kind of chacters they contain.
 * 
 * @author siegel
 * 
 */
public interface StringLiteral {

	/**
	 * The different kinds of strings, based on the kind of characters they
	 * contain.
	 * 
	 * @author siegel
	 * 
	 */
	public enum StringKind {
		CHAR, WCHAR, CHAR16, CHAR32, UTF_8
	}

	/**
	 * Returns the number of execution characters in the string.
	 * 
	 * @return the number of execution characters
	 */
	public int getNumCharacters();

	/**
	 * Returns the index-th execution character in the string.
	 * 
	 * @param index
	 *            the character index, an integer in the range [0,n), where n is
	 *            number of execution characters
	 * @return the index-th execution character
	 */
	public ExecutionCharacter getCharacter(int index);

	/**
	 * Returns the kind of string this is.
	 * 
	 * @return the kind of this string
	 */
	public StringKind getStringKind();

}
