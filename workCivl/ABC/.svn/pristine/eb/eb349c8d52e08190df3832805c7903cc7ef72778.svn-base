package edu.udel.cis.vsl.abc.front.c.preproc;

import org.antlr.runtime.tree.Tree;

import edu.udel.cis.vsl.abc.token.IF.Formation;
import edu.udel.cis.vsl.abc.token.IF.SourceFile;

/**
 * A class which records information related to a source file that is parsed by
 * the preprocessor.
 * 
 * @author siegel
 * 
 */
public class PreprocessorSourceFileInfo {

	private Formation history;

	private PreprocessorParser parser;

	private Tree tree;

	private Tree position;

	public PreprocessorSourceFileInfo(Formation history,
			PreprocessorParser parser, Tree tree, Tree position) {
		this.history = history;
		this.parser = parser;
		this.tree = tree;
		this.position = position;
	}

	public Formation getIncludeHistory() {
		return history;
	}

	public SourceFile getFile() {
		return history.getLastFile();
	}

	public PreprocessorParser getParser() {
		return parser;
	}

	public Tree getTree() {
		return tree;
	}

	public Tree getPosition() {
		return position;
	}

	public void setPosition(Tree position) {
		this.position = position;
	}
}
