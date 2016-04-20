package edu.udel.cis.vsl.abc.token.common;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import edu.udel.cis.vsl.abc.token.IF.CivlcToken;
import edu.udel.cis.vsl.abc.token.IF.CharacterToken;
import edu.udel.cis.vsl.abc.token.IF.ExecutionCharacter;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.token.IF.TokenFactory;
import edu.udel.cis.vsl.abc.token.IF.UnsourcedException;
import edu.udel.cis.vsl.abc.token.IF.ExecutionCharacter.CharacterKind;
import edu.udel.cis.vsl.abc.token.IF.StringLiteral.StringKind;

/**
 * A class to help parsing of characters and string and creation of
 * corresponding tokens.
 * 
 * @author siegel
 * 
 */
public class CommonCharacterFactory {

	// Types...

	/**
	 * A type which extracts the "core" part of the text of a string literal
	 * token (the text minus the optional prefix and double quotes) and which
	 * records the kind of string (which is determined by the prefix).
	 * 
	 * @author siegel
	 */
	private class StringAnalysis {
		CivlcToken token;
		StringKind kind;
		String core;

		StringAnalysis(CivlcToken token, StringKind kind, String core) {
			this.token = token;
			this.kind = kind;
			this.core = core;
		}
	}

	/**
	 * A type used to help parse the characters from a string, one at a time.
	 * */
	private class CharacterParseData {
		String string;
		int totalLength;
		CharacterKind kind;
		int index;

		CharacterParseData(String string, CharacterKind kind) {
			this.string = string;
			this.kind = kind;
			this.index = 0;
			this.totalLength = string.length();
		}
	}

	// Fields...

	/**
	 * The tokenFactory which this class is helping.
	 */
	private TokenFactory tokenFactory;

	/**
	 * A map used to implement the Flyweight Patten on ExecutionCharacters.
	 */
	private Map<ExecutionCharacter, ExecutionCharacter> characterMap = new HashMap<ExecutionCharacter, ExecutionCharacter>();

	// Constructors...

	/**
	 * Constructs new CommonCharacterFactory associated to given tokenFactory.
	 * 
	 * @param tokenFactory
	 *            any TokenFactory
	 */
	public CommonCharacterFactory(TokenFactory tokenFactory) {
		this.tokenFactory = tokenFactory;
	}

	// Exported methods...

	/**
	 * Returns canonic instance of execution character with given parameters.
	 * 
	 * @param kind
	 *            the character kind
	 * @param codePoint
	 *            the Unicode code point for this character
	 * @param characters
	 *            the (1 or 2) Java character(s) representing this code point
	 * @return the execution character specified by the given 3 parameters
	 */
	public ExecutionCharacter executionCharacter(CharacterKind kind,
			int codePoint, char[] characters) {
		ExecutionCharacter result = new CommonExecutionCharacter(kind,
				codePoint, characters);
		ExecutionCharacter old = characterMap.get(result);

		if (old == null) {
			characterMap.put(result, result);
			return result;
		}
		return old;
	}

	public ExecutionCharacter nullChar(CharacterKind kind) {
		return executionCharacter(kind, 0, new char[] { '\0' });
	}

	/**
	 * Given a CToken of type CHARACTER_CONSTANT, this returns an instance of
	 * CommonCharacterToken formed by analyzing the given token. The text from
	 * the given token is analyzed to extract its (optional) prefix, used to
	 * determine the "character kind", escape sequences are analyzed, and so on.
	 * 
	 * @param token
	 *            a token of type PreprocessorParser.CHARACTER_CONSTANT;
	 * @return a CharacterToken based on data in the given token
	 * @throws SyntaxException
	 *             if the text of the character constant is not well formed
	 */
	public CharacterToken characterToken(CivlcToken token) throws SyntaxException {
		String text = token.getText();
		Character prefix = text.charAt(0);
		CharacterKind kind;
		String stripped;
		int length;
		ExecutionCharacter executionCharacter;
		CharacterParseData data;

		if (prefix == 'L' || prefix == 'u' || prefix == 'U') {
			stripped = text.substring(1);
			if (prefix == 'L')
				kind = CharacterKind.WCHAR;
			else if (prefix == 'u')
				kind = CharacterKind.CHAR16;
			else if (prefix == 'U')
				kind = CharacterKind.CHAR32;
			else
				throw new RuntimeException("unreachable");
		} else {
			kind = CharacterKind.CHAR;
			stripped = text;
		}
		length = stripped.length();
		if (length < 3 || stripped.charAt(0) != '\''
				|| stripped.charAt(length - 1) != '\'')
			throw tokenFactory.newSyntaxException(
					"Malformed character constant: " + stripped, token);
		stripped = stripped.substring(1, length - 1);
		length -= 2;
		data = new CharacterParseData(stripped, kind);
		try {
			executionCharacter = parseNextCharacter(data);
		} catch (UnsourcedException e) {
			throw tokenFactory.newSyntaxException(
					"Malformed character constant", token);
		}
		if (data.index != data.totalLength)
			throw tokenFactory.newSyntaxException(
					"Malformed character constant", token);
		return new CommonCharacterToken(token, executionCharacter);
	}

	/**
	 * Given a CToken of type STRING_LITERAL, this method analyzes the text of
	 * the string literal and uses the result to create a StringLiteral object.
	 * The StringLiteral object stores the "string kind" of the string literal
	 * (determined by the optional prefix in the text) and the sequence of
	 * execution characters specified by the core part of the test.
	 * 
	 * The null character is appended to the execution character sequence.
	 * 
	 * @param token
	 *            a token of type STRING_LITERAL
	 * @return a StringLiteral object with kind and execution characters
	 *         determined by the text of the given token
	 * @throws SyntaxException
	 *             if the text of given token does not have the proper syntax
	 *             for a string literal
	 */
	public CommonStringLiteral stringLiteral(CivlcToken token)
			throws SyntaxException {
		StringAnalysis analysis = stringAnalyze(token);
		StringKind stringKind = analysis.kind;
		CharacterKind characterKind = characterKind(stringKind);
		ArrayList<ExecutionCharacter> characters = new ArrayList<ExecutionCharacter>();

		try {
			extractCharacters(characterKind, analysis.core, characters);
		} catch (UnsourcedException e) {
			throw tokenFactory.newSyntaxException(e, token);
		}
		characters.add(nullChar(characterKind));
		return new CommonStringLiteral(stringKind, characters);
	}

	/**
	 * Given a sequence of adjacent tokens, all of type STRING_LITERAL, this
	 * forms the StringLiteral object obtained by (1) analyzing each token to
	 * extract a sequence of execution characters, and (2) then concatenating
	 * the sequences to form one big sequence of execution characters. The
	 * string kind of the result is determined by the kinds of the constituents
	 * as specified in the C11 Standard.
	 * 
	 * The null character is appended to the final execution character sequence.
	 * 
	 * @param tokens
	 *            a list of tokens, each of type STRING_LITERAL
	 * @return a StringLiteral object representing the concatenation of the
	 *         StringLiteral objects resulting from each token
	 * @throws SyntaxException
	 *             if any of the token texts are not proper string literals, or
	 *             the string kinds do not match up
	 */
	public CommonStringLiteral stringLiteral(List<CivlcToken> tokens)
			throws SyntaxException {
		List<StringAnalysis> analyses = new LinkedList<StringAnalysis>();
		ArrayList<ExecutionCharacter> characters = new ArrayList<ExecutionCharacter>();
		StringKind stringKind;
		CharacterKind characterKind;

		for (CivlcToken token : tokens)
			analyses.add(stringAnalyze(token));
		stringKind = concatKind(analyses);
		characterKind = characterKind(stringKind);
		for (StringAnalysis analysis : analyses) {
			try {
				extractCharacters(characterKind, analysis.core, characters);
			} catch (UnsourcedException e) {
				throw tokenFactory.newSyntaxException(e, analysis.token);
			}
		}
		characters.add(nullChar(characterKind));
		return new CommonStringLiteral(stringKind, characters);
	}

	// Private methods...

	private void extractCharacters(CharacterKind kind, String text,
			ArrayList<ExecutionCharacter> list) throws UnsourcedException {
		CharacterParseData data = new CharacterParseData(text, kind);

		while (data.index < data.totalLength)
			list.add(parseNextCharacter(data));
	}

	private StringAnalysis stringAnalyze(CivlcToken token) throws SyntaxException {
		String text = token.getText();
		int length = text.length();
		char prefix0;
		int quotePos;
		StringKind kind;

		if (length < 2)
			throw tokenFactory.newSyntaxException("Malformed string literal",
					token);
		if (text.charAt(length - 1) != '"')
			throw tokenFactory.newSyntaxException("Malformed string literal",
					token);
		prefix0 = text.charAt(0);
		switch (prefix0) {
		case '"':
			kind = StringKind.CHAR;
			quotePos = 0;
			break;
		case 'L':
			kind = StringKind.WCHAR;
			quotePos = 1;
			break;
		case 'U':
			kind = StringKind.CHAR32;
			quotePos = 1;
			break;
		case 'u': {
			char prefix1 = text.charAt(1);

			switch (prefix1) {
			case '"':
				kind = StringKind.CHAR16;
				quotePos = 1;
				break;
			case '8':
				kind = StringKind.UTF_8;
				quotePos = 2;
				break;
			default:
				throw tokenFactory.newSyntaxException("Illegal string prefix",
						token);
			}
			break;
		}
		default:
			throw tokenFactory.newSyntaxException("Illegal string prefix",
					token);
		}
		if (length < quotePos + 2)
			throw tokenFactory.newSyntaxException("Malformed string literal",
					token);
		if (text.charAt(quotePos) != '"')
			throw tokenFactory.newSyntaxException(
					"String literal missing open quote", token);
		return new StringAnalysis(token, kind, text.substring(quotePos + 1,
				length - 1));
	}

	private StringKind concatKind(List<StringAnalysis> analyses)
			throws SyntaxException {
		StringKind kind = null;

		for (StringAnalysis analysis : analyses) {
			if (kind == null) {
				kind = analysis.kind;
			} else {
				StringKind newKind = analysis.kind;

				if (kind != newKind) {
					if (kind == StringKind.CHAR)
						kind = newKind;
					else if (newKind != StringKind.CHAR)
						throw tokenFactory
								.newSyntaxException(
										"Adjacent string literals have incompatible types: "
												+ kind + ", " + newKind,
										analysis.token);
				}
			}
		}
		return kind;
	}

	private CharacterKind characterKind(StringKind stringKind) {
		switch (stringKind) {
		case CHAR:
		case UTF_8:
			return CharacterKind.CHAR;
		case WCHAR:
			return CharacterKind.WCHAR;
		case CHAR16:
			return CharacterKind.CHAR16;
		case CHAR32:
			return CharacterKind.CHAR32;
		default:
			throw new RuntimeException("unreachable");
		}
	}

	private boolean isHex(char c) {
		return '0' <= c && c <= '9' || 'a' <= c && c <= 'f' || 'A' <= c
				&& c <= 'F';
	}

	private boolean isOctal(char c) {
		return '0' <= c && c <= '7';
	}

	private ExecutionCharacter parseNextCharacter(CharacterParseData data)
			throws UnsourcedException {
		String text = data.string;
		int index = data.index;
		int totalLength = data.totalLength;
		char first = text.charAt(index);
		int codePoint;
		char[] characters;

		// cases: (1) single char (2) escape sequence (3) \ followed by
		// 1, 2, or 3 octal digits, or (4) \x followed by sequence
		// of hex digits. Read maximal substring that matches
		// one of those patterns.

		index++; // consumed first character
		if (first == '\\') {
			char second;

			if (index >= totalLength)
				throw tokenFactory
						.newUnsourcedException("Malformed character constant: "
								+ text);
			second = text.charAt(index);
			index++; // consume second
			if (second == 'x') { // hex: sequence of hex digits
				int start = index;
				String hexString;

				// consume all hex digits...
				while (index < totalLength && isHex(text.charAt(index)))
					index++;
				hexString = text.substring(start, index);
				try {
					codePoint = Integer.parseInt(hexString, 16);
				} catch (NumberFormatException e) {
					throw tokenFactory
							.newUnsourcedException("Malformed character constant: "
									+ text);
				}
				characters = Character.toChars(codePoint);
			} else if (isOctal(second)) { // octal: 1, 2, or 3 digits
				int start = index - 1;
				String octalString;

				if (index < totalLength && isOctal(text.charAt(index))) {
					index++; // consume second octal digit
					if (index < totalLength && isOctal(text.charAt(index)))
						index++; // consume third octal digit
				}
				octalString = text.substring(start, index);
				try {
					codePoint = Integer.parseInt(octalString, 8);
				} catch (NumberFormatException e) {
					throw tokenFactory
							.newUnsourcedException("Malformed character constant: "
									+ text);
				}
				characters = Character.toChars(codePoint);
			} else { // escape sequence
				characters = new char[1];
				switch (second) {
				case '\'':
					characters[0] = '\'';
					break;
				case '"':
					characters[0] = '"';
					break;
				case '?':
					characters[0] = '?';
					break;
				case '\\':
					characters[0] = '\\';
					break;
				case 'a':
					characters[0] = '\007'; // alert
					break;
				case 'b':
					characters[0] = '\b'; // backspace
					break;
				case 'f':
					characters[0] = '\f'; // formfeed
					break;
				case 'n':
					characters[0] = '\n'; // newline
					break;
				case 'r':
					characters[0] = '\r'; // return
					break;
				case 't':
					characters[0] = '\t'; // tab
					break;
				case 'v':
					characters[0] = '\013'; // vertical tab
					break;
				default:
					throw tokenFactory
							.newUnsourcedException("Unknown escape sequence in character");
				}
				codePoint = (int) characters[0];
			}
		} else {
			characters = new char[] { first };
			codePoint = (int) first;
		}
		data.index = index;
		return executionCharacter(data.kind, codePoint, characters);
	}

}
