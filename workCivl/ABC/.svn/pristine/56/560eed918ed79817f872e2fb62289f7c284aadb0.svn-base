package edu.udel.cis.vsl.abc.token.common;

import java.util.Arrays;

import edu.udel.cis.vsl.abc.token.IF.ExecutionCharacter;

public class CommonExecutionCharacter implements ExecutionCharacter {

	private final static int classCode = CommonExecutionCharacter.class
			.hashCode();

	private CharacterKind kind;

	private int codePoint;

	private char[] characters;

	public CommonExecutionCharacter(CharacterKind kind, int codePoint,
			char[] characters) {
		assert kind != null;
		assert characters != null;
		this.kind = kind;
		this.codePoint = codePoint;
		this.characters = characters;
	}

	@Override
	public CharacterKind getCharacterKind() {
		return kind;
	}

	@Override
	public int getCodePoint() {
		return codePoint;
	}

	@Override
	public char[] getCharacters() {
		return characters;
	}

	@Override
	public boolean equals(Object object) {
		if (this == object)
			return true;
		if (object instanceof CommonExecutionCharacter) {
			CommonExecutionCharacter that = (CommonExecutionCharacter) object;

			return kind == that.kind && codePoint == that.codePoint
					&& Arrays.equals(characters, that.characters);
		}
		return false;
	}

	@Override
	public int hashCode() {
		return classCode + kind.hashCode() + codePoint
				+ Arrays.hashCode(characters);
	}

	@Override
	public String rawString() {
		int length = characters.length;

		if (length == 1) {
			char c = characters[0];

			switch (c) {
			case 0:
				return "\\0";
			case '\'':
				return "\\\'";
			case '\b':
				return "\\b";
			case '\f':
				return "\\f";
			case '\n':
				return "\\n";
			case '\r':
				return "\\r";
			case '\t':
				return "\\t";
			case '\013':
				return "\\v";
			case ' ':
				return " ";
			case '\007':
				return "\\a";
			default:
			}
			return Character.toString(c);
		} else {
			return "'" + Integer.toHexString(codePoint) + "'";
		}
	}

	@Override
	public String toString() {
		int length = characters.length;

		if (length == 1) {
			char c = characters[0];

			switch (c) {
			case 0:
				return "'\\0'";
			case '\'':
				return "'\\\''";
			case '\b':
				return "'\\b'";
			case '\f':
				return "'\\f'";
			case '\n':
				return "'\\n'";
			case '\r':
				return "'\\r'";
			case '\t':
				return "'\\t'";
			case '\013':
				return "'\\v'";
			case ' ':
				return "' '";
			case '\007':
				return "'\\a'";
			default:
			}
			return Character.toString(c);
		} else {
			return "'" + Integer.toHexString(codePoint) + "'";
		}
	}

}
