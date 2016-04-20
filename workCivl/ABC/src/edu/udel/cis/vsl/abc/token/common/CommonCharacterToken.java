package edu.udel.cis.vsl.abc.token.common;

import edu.udel.cis.vsl.abc.token.IF.CivlcToken;
import edu.udel.cis.vsl.abc.token.IF.CharacterToken;
import edu.udel.cis.vsl.abc.token.IF.ExecutionCharacter;

public class CommonCharacterToken extends CommonCivlcToken implements
		CharacterToken {

	/**
	 * Eclipse make me do it.
	 */
	private static final long serialVersionUID = 4443038776536972250L;

	private ExecutionCharacter character;

	public CommonCharacterToken(CivlcToken token, ExecutionCharacter character) {
		super(token, token.getFormation());
		assert character != null;
		this.character = character;
		this.setNext(token.getNext());
		this.setTokenIndex(token.getTokenIndex());
		if (!token.isExpandable())
			this.makeNonExpandable();
	}

	@Override
	public ExecutionCharacter getExecutionCharacter() {
		return character;
	}

}
