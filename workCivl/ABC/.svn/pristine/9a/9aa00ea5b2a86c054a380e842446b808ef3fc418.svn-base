package edu.udel.cis.vsl.abc.front.fortran.preproc;

import java.util.List;

import edu.udel.cis.vsl.abc.token.IF.CivlcToken;
import edu.udel.cis.vsl.abc.token.IF.CivlcTokenSource;
import edu.udel.cis.vsl.abc.token.IF.TokenFactory;
import edu.udel.cis.vsl.abc.token.common.CommonCivlcTokenSource;

public class FortranTokenSource extends CommonCivlcTokenSource implements
		CivlcTokenSource {

	private FortranTokenStream tokenStream;

	public FortranTokenSource(List<CivlcToken> tokens, TokenFactory factory,
			FortranTokenStream tokenStream) {
		super(tokens, factory);
		this.tokenStream = tokenStream;
	}

	public FortranTokenStream getTokenStream() {
		return tokenStream;
	}
}
