package edu.udel.cis.vsl.abc.ast.type.common;

import java.io.PrintStream;
import java.util.Map;

import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;

public class CommonBasicType extends CommonObjectType implements
		StandardBasicType {

	private static int classCode = CommonBasicType.class.hashCode();

	private BasicTypeKind basicTypeKind;

	public CommonBasicType(BasicTypeKind basicTypeKind) {
		super(TypeKind.BASIC);
		this.basicTypeKind = basicTypeKind;
	}

	@Override
	public BasicTypeKind getBasicTypeKind() {
		return basicTypeKind;
	}

	@Override
	public boolean isComplete() {
		return true;
	}

	@Override
	public boolean isVariablyModified() {
		return false;
	}

	public boolean isSigned() {
		switch (basicTypeKind) {
		case SIGNED_CHAR:
		case SHORT:
		case INT:
		case LONG:
		case LONG_LONG:
			return true;
		default:
			return false;
		}
	}

	public boolean isUnsigned() {
		switch (basicTypeKind) {
		case BOOL:
		case UNSIGNED_CHAR:
		case UNSIGNED_SHORT:
		case UNSIGNED:
		case UNSIGNED_LONG:
		case UNSIGNED_LONG_LONG:
			return true;
		default:
			return false;
		}
	}

	@Override
	public boolean isInteger() {
		return isSigned() || isUnsigned()
				|| basicTypeKind == BasicTypeKind.CHAR;
	}

	@Override
	public boolean isFloating() {
		switch (basicTypeKind) {
		case FLOAT:
		case DOUBLE:
		case LONG_DOUBLE:
		case FLOAT_COMPLEX:
		case DOUBLE_COMPLEX:
		case LONG_DOUBLE_COMPLEX:
			return true;
		default:
			return false;
		}
	}

	@Override
	public boolean isEnumeration() {
		return false;
	}

	@Override
	public boolean inRealDomain() {
		switch (basicTypeKind) {
		case FLOAT_COMPLEX:
		case DOUBLE_COMPLEX:
		case LONG_DOUBLE_COMPLEX:
			return false;
		default:
			return true;
		}
	}

	@Override
	public boolean inComplexDomain() {
		return !inRealDomain();
	}

	@Override
	public int hashCode() {
		return classCode + basicTypeKind.hashCode();
	}

	@Override
	public boolean equals(Object object) {
		if (this == object)
			return true;
		if (object instanceof CommonBasicType) {
			CommonBasicType that = (CommonBasicType) object;

			return that.basicTypeKind == this.basicTypeKind;
		}
		return false;
	}

	@Override
	public String toString() {
		switch (basicTypeKind) {
		case BOOL:
			return "_Bool";
		case CHAR:
			return "char";
		case DOUBLE:
			return "double";
		case DOUBLE_COMPLEX:
			return "double _Complex";
		case FLOAT:
			return "float";
		case FLOAT_COMPLEX:
			return "float _Complex";
		case INT:
			return "int";
		case LONG:
			return "long";
		case LONG_DOUBLE:
			return "long double";
		case LONG_DOUBLE_COMPLEX:
			return "long double _Complex";
		case LONG_LONG:
			return "long long";
		case REAL:
			return "$real";
		case SHORT:
			return "short";
		case SIGNED_CHAR:
			return "signed char";
		case UNSIGNED:
			return "unsigned";
		case UNSIGNED_CHAR:
			return "unsigned char";
		case UNSIGNED_LONG:
			return "unsigned long";
		case UNSIGNED_LONG_LONG:
			return "unsigned long long";
		case UNSIGNED_SHORT:
			return "unsignd short";
		default:
			throw new RuntimeException("Unreachable");
		}
	}

	@Override
	public void print(String prefix, PrintStream out, boolean abbrv) {
		out.print(this);
	}

	@Override
	public boolean isScalar() {
		return true;
	}

	@Override
	protected boolean similar(Type other, boolean equivalent,
			Map<TypeKey, Type> seen) {
		return equals(other);
	}

}
