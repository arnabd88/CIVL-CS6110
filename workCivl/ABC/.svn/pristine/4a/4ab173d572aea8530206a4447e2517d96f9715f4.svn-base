package edu.udel.cis.vsl.abc.token.common;

import java.io.File;

import edu.udel.cis.vsl.abc.token.IF.Formation;
import edu.udel.cis.vsl.abc.token.IF.SourceFile;

/**
 * This formation is used to represent the formation of a token through some
 * "system" means, instead of token derived from a source file.
 * 
 * @author siegel
 * 
 */
public class SystemFormation implements Formation {

	private String identifier;

	private SourceFile file;

	public SystemFormation(String identifier, int index) {
		this.identifier = identifier;
		this.file = new SourceFile(new File(identifier), index);
	}

	@Override
	public String suffix() {
		return identifier;
	}

	@Override
	public SourceFile getLastFile() {
		return file;
	}

}
