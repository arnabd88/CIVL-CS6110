package edu.udel.cis.vsl.abc.token.common;

import org.antlr.runtime.Token;

import edu.udel.cis.vsl.abc.token.IF.CivlcToken;
import edu.udel.cis.vsl.abc.token.IF.Macro;
import edu.udel.cis.vsl.abc.token.IF.MacroExpansion;
import edu.udel.cis.vsl.abc.token.IF.SourceFile;

public class CommonMacroExpansion implements MacroExpansion {

	/**
	 * The token that is being expanded by the macro.
	 */
	private CivlcToken startToken;

	/**
	 * The macro doing the expanding. Its name should be the same as the text of
	 * the startToken.
	 */
	private Macro macro;

	/**
	 * The index of the token resulting from the expansion in the list of
	 * replacement tokens for the macro. In other words, the end token is the
	 * index-th replacement token from macro's replacement list.
	 */
	private int index;

	CommonMacroExpansion(CivlcToken startToken, Macro macro, int index) {
		this.startToken = startToken;
		this.macro = macro;
		this.index = index;
	}

	@Override
	public String suffix() {
		return " from " + startToken.toString();
	}

	@Override
	public String toString() {
		return "MacroExpansion[" + startToken.getText() + ", "
				+ macro.getName() + ", " + index + "]";
	}

	@Override
	public CivlcToken getStartToken() {
		return startToken;
	}

	@Override
	public Macro getMacro() {
		return macro;
	}

	@Override
	public int getReplacementTokenIndex() {
		return index;
	}

	@Override
	public Token getReplacementToken() {
		return macro.getReplacementToken(index);
	}

	@Override
	public SourceFile getLastFile() {
		return macro.getFile();
	}

}
