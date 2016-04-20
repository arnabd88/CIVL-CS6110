package edu.udel.cis.vsl.abc.token.common;

import java.util.ArrayList;

import edu.udel.cis.vsl.abc.token.IF.CivlcToken;
import edu.udel.cis.vsl.abc.token.IF.Concatenation;
import edu.udel.cis.vsl.abc.token.IF.SourceFile;

public class CommonConcatenation implements Concatenation {

	private ArrayList<CivlcToken> constituents;

	public CommonConcatenation(ArrayList<CivlcToken> constituents) {
		assert constituents != null;
		assert constituents.size() >= 1;
		this.constituents = constituents;
	}

	@Override
	public String suffix() {
		String result = " from concatenation of the following "
				+ getNumConstituents() + " tokens:";

		for (CivlcToken token : constituents)
			result += "\n" + token;
		return result;
	}

	@Override
	public SourceFile getLastFile() {
		return constituents.get(0).getSourceFile();
	}

	@Override
	public int getNumConstituents() {
		return constituents.size();
	}

	@Override
	public CivlcToken getConstituent(int index) {
		return constituents.get(index);
	}

	// @Override
	// public String fileShortName() {
	// return constituents.get(0).getFileShortName();
	// }

}
