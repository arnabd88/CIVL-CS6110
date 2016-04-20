package edu.udel.cis.vsl.abc.ast.node.common;

import edu.udel.cis.vsl.abc.ast.node.IF.AttributeKey;

public class CommonAttributeKey implements AttributeKey {

	private String name;

	private int id;

	private Class<? extends Object> attributeClass;

	public CommonAttributeKey(int id, String name,
			Class<? extends Object> attributeClass) {
		this.id = id;
		this.name = name;
		this.attributeClass = attributeClass;
	}

	@Override
	public String getAttributeName() {
		return name;
	}

	@Override
	public Class<? extends Object> getAttributeClass() {
		return attributeClass;
	}

	public int getId() {
		return id;
	}

}
