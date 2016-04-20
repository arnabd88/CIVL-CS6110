package edu.udel.cis.vsl.abc.transform.IF;

import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;

public abstract class TransformRecord {

	public String code;

	public String name;

	public String shortDescription;

	public TransformRecord(String code, String name, String shortDescription) {
		this.code = code;
		this.name = name;
		this.shortDescription = shortDescription;
	}

	public abstract Transformer create(ASTFactory astFactory);
}
