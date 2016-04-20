package edu.udel.cis.vsl.civl.model.common.type;

import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.type.StructOrUnionField;

public class CommonStructField implements StructOrUnionField {

	private int index = -1;
	private Identifier name;
	private CIVLType type;

	public CommonStructField(Identifier name, CIVLType type) {
		this.name = name;
		this.type = type;
	}

	@Override
	public Identifier name() {
		return name;
	}

	@Override
	public CIVLType type() {
		return type;
	}

	@Override
	public int index() {
		return index;
	}

	@Override
	public String toString() {
		return name + " : " + type;
	}

	void setIndex(int index) {
		this.index = index;
	}

}
