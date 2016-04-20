package edu.udel.cis.vsl.abc.analysis.entity;

import edu.udel.cis.vsl.abc.token.IF.Source;

/**
 * A Navigator is a reference to an immediate member of compound literal object.
 * It comprises a type (the type of the compound literal object) and an integer
 * index (the index of the member of that object).
 * 
 * @author siegel
 * 
 */
public class Navigator {

	/**
	 * Source code reference for error reporting.
	 */
	private Source source;

	/**
	 * The index of the member of the object to which this navigator applies.
	 */
	private int index;

	public Navigator(int index, Source source) {
		this.index = index;
		this.source = source;
	}

	public int getIndex() {
		return index;
	}

	@Override
	public String toString() {
		return "[" + index + "]";
	}

	public Source getSource() {
		return source;
	}

}
