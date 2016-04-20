package edu.udel.cis.vsl.abc.ast.value.common;

import edu.udel.cis.vsl.abc.ast.type.IF.IntegerType;
import edu.udel.cis.vsl.abc.ast.value.IF.CharacterValue;
import edu.udel.cis.vsl.abc.ast.value.IF.ValueFactory.Answer;
import edu.udel.cis.vsl.abc.token.IF.ExecutionCharacter;

public class CommonCharacterValue extends CommonValue implements CharacterValue {

	private final static int classCode = CommonCharacterValue.class.hashCode();

	private ExecutionCharacter character;

	public CommonCharacterValue(IntegerType type, ExecutionCharacter character) {
		super(type);
		assert character != null;
		this.character = character;
	}

	@Override
	public boolean equals(Object object) {
		if (this == object)
			return true;
		if (object instanceof CommonCharacterValue) {
			CommonCharacterValue that = (CommonCharacterValue) object;

			return getType().equals(that.getType())
					&& character.equals(that.character);
		}
		return false;
	}

	@Override
	public int hashCode() {
		return classCode + getType().hashCode() + character.hashCode();
	}

	@Override
	public ExecutionCharacter getCharacter() {
		return character;
	}

	@Override
	public Answer isZero() {
		return character.getCodePoint() == 0 ? Answer.YES : Answer.NO;
	}

	@Override
	public String toString() {
		return character.toString();
	}

}
