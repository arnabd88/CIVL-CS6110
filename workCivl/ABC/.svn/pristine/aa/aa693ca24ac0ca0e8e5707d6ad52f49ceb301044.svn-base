package edu.udel.cis.vsl.abc.token.common;

import java.util.ArrayList;

import edu.udel.cis.vsl.abc.token.IF.ExecutionCharacter;
import edu.udel.cis.vsl.abc.token.IF.StringLiteral;

public class CommonStringLiteral implements StringLiteral {

	private StringKind stringKind;

	private ArrayList<ExecutionCharacter> characters;

	public CommonStringLiteral(StringKind kind,
			ArrayList<ExecutionCharacter> characters) {
		this.stringKind = kind;
		this.characters = characters;
	}

	@Override
	public boolean equals(Object object) {
		if (this == object)
			return true;
		if (object instanceof CommonStringLiteral) {
			CommonStringLiteral that = (CommonStringLiteral) object;
			int numChars = getNumCharacters();

			if (stringKind != that.stringKind
					|| getNumCharacters() != that.getNumCharacters())
				return false;
			for (int i = 0; i < numChars; i++) {
				if (!this.getCharacter(i).equals(that.getCharacter(i)))
					return false;
			}
			return true;
		}
		return false;
	}

	@Override
	public int getNumCharacters() {
		return characters.size();
	}

	@Override
	public ExecutionCharacter getCharacter(int index) {
		return characters.get(index);
	}

	@Override
	public StringKind getStringKind() {
		return stringKind;
	}

	@Override
	public String toString() {
		StringBuffer result = new StringBuffer();

		result.append('"');
		for (ExecutionCharacter ec : characters)
			if (ec.getCodePoint() != 0)
				result.append(ec.rawString());
		result.append('"');
		return result.toString();
		// return characters.toString();
	}

}
