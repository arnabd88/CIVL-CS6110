package edu.udel.cis.vsl.abc.token.common;

import edu.udel.cis.vsl.abc.token.IF.CivlcToken;
import edu.udel.cis.vsl.abc.token.IF.Inclusion;
import edu.udel.cis.vsl.abc.token.IF.SourceFile;

public class CommonInclusion implements Inclusion {

	/**
	 * The file included. Always non-null.
	 */
	private SourceFile file;

	/**
	 * The token containing the file name in the include directive that named
	 * the file. Will be null for the original file (which wasn't included from
	 * anything).
	 */
	private CivlcToken includeToken;

	public CommonInclusion(SourceFile file) {
		assert file != null;
		this.file = file;
		this.includeToken = null;
	}

	public CommonInclusion(SourceFile file, CivlcToken includeToken) {
		assert file != null;
		this.file = file;
		this.includeToken = includeToken;
	}

	@Override
	public String suffix() {
		if (includeToken != null)
			return " included from " + includeToken;
		else
			return "";
	}

	@Override
	public SourceFile getLastFile() {
		return file;
	}

	@Override
	public SourceFile getFile() {
		return file;
	}

	@Override
	public CivlcToken getIncludeToken() {
		return includeToken;
	}

}
