package edu.udel.cis.vsl.abc.ast.type.common;

import java.io.PrintStream;
import java.util.Map;

import edu.udel.cis.vsl.abc.ast.type.IF.DomainType;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;

public class CommonDomainType extends CommonObjectType implements DomainType {

	private final static int classCode = CommonDomainType.class.hashCode();

	int dimension = -1;

	public CommonDomainType() {
		super(TypeKind.DOMAIN);
	}

	public CommonDomainType(int dimension) {
		super(TypeKind.DOMAIN);
		assert dimension >= 1;
		this.dimension = dimension;

	}

	@Override
	public boolean compatibleWith(Type type) {
		if (type instanceof DomainType) {
			DomainType that = (DomainType) type;

			if (this.hasDimension() && that.hasDimension())
				return this.getDimension() == that.getDimension();
			return true;
		}
		return false;
	}

	@Override
	public void print(String prefix, PrintStream out, boolean abbrv) {
		out.print("$domain");
		if (hasDimension())
			out.print("(" + dimension + ")");
	}

	@Override
	public boolean isScalar() {
		return false;
	}

	@Override
	public boolean hasDimension() {
		return dimension > 0;
	}

	@Override
	public int getDimension() {
		return dimension;
	}

	@Override
	public boolean isVariablyModified() {
		return false;
	}

	@Override
	public int hashCode() {
		int result = classCode;

		if (dimension > 0)
			result += 97 * dimension;
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof CommonDomainType) {
			CommonDomainType that = (CommonDomainType) obj;

			return dimension == that.dimension;
		}
		return false;
	}

	@Override
	public String toString() {
		String result = "$domain";

		if (hasDimension())
			result += "(" + dimension + ")";
		return result;
	}

	@Override
	public boolean isComplete() {
		return true;
	}

	@Override
	protected boolean similar(Type other, boolean equivalent,
			Map<TypeKey, Type> seen) {
		if (equivalent)
			return equals(other);
		else
			return compatibleWith(other);
	}

}
