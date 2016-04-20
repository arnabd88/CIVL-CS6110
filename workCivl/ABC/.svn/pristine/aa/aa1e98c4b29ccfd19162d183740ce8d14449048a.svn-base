package edu.udel.cis.vsl.abc.token.common;

import edu.udel.cis.vsl.abc.token.IF.CivlcToken;
import edu.udel.cis.vsl.abc.token.IF.Formation;
import edu.udel.cis.vsl.abc.token.IF.StringLiteral;
import edu.udel.cis.vsl.abc.token.IF.StringToken;

public class CommonStringToken extends CommonCivlcToken implements StringToken {

	/**
	 * Eclipse made me do it.
	 */
	private static final long serialVersionUID = 6839260551000953066L;

	private StringLiteral literal;

	public CommonStringToken(int type, Formation formation,
			StringLiteral literal) {
		super(type, literal.toString(), formation);
		this.literal = literal;
	}

	public CommonStringToken(CivlcToken token, Formation formation,
			StringLiteral data) {
		super(token, formation);
		this.literal = data;
	}

	@Override
	public StringLiteral getStringLiteral() {
		return literal;
	}

}
