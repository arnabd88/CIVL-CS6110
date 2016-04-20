package edu.udel.cis.vsl.abc.token.IF;

public interface ExecutionCharacter {

	public enum CharacterKind {
		CHAR, WCHAR, CHAR16, CHAR32
	};

	CharacterKind getCharacterKind();

	/**
	 * Returns the Unicode "code point" for the character represented by this
	 * literal node. Unicode assigns an integer value to each abstract character
	 * in the range 0 to 10ffff (hex). That integer is called a "code point".
	 * Code points 0 through FF agree with ASCII.
	 */
	int getCodePoint();

	/**
	 * Returns the Java char representation of this unicode character. Java uses
	 * 2 bytes to represent a char. Hence a single Java char cannot represent
	 * every Unicode code point, but it can represent those in the
	 * "Basic Multilingual Plan" ("BMP"), i.e., code points 0000-FFFF.
	 * 
	 * If this unicode character falls in the BMP range, then this array has
	 * length 1 and its sole element is the Java character representing the
	 * unicode character. Otherwise, this array has length 2, and the two Java
	 * characters together represent the Unicode character, in a way specified
	 * by the Java language; see the API documentation for class Character.
	 */
	char[] getCharacters();

	/**
	 * A string representation of the character without any surrounding
	 * quotation marks. Typically one character, but for special characters
	 * (like newlines, tabs, etc.) this string will be an escape sequence like
	 * "\n" (without the quotes).
	 * 
	 * @return string representation, stripped down
	 */
	String rawString();

}
