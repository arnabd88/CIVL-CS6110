package edu.udel.cis.vsl.abc.ast.type.common;

public class TypeKey {

	private CommonType type;

	public TypeKey(CommonType type) {
		this.type = type;
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof TypeKey) {
			TypeKey that = (TypeKey) obj;

			return type == that.type;
		}
		return false;
	}

	@Override
	public int hashCode() {
		return type.objectCode();
	}

}
