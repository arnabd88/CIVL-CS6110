package edu.udel.cis.vsl.abc.ast.type.common;

import java.io.PrintStream;
import java.util.Map;

import edu.udel.cis.vsl.abc.ast.type.IF.QualifiedObjectType;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.ast.type.IF.UnqualifiedObjectType;

public class CommonQualifiedObjectType extends CommonObjectType implements
		QualifiedObjectType {

	private UnqualifiedObjectType baseType;

	private boolean constQualified = false;

	private boolean volatileQualified = false;

	private boolean restrictQualified = false;

	private boolean inputQualified = false;

	private boolean outputQualified = false;

	public CommonQualifiedObjectType(UnqualifiedObjectType baseType,
			boolean constQualified, boolean volatileQualified,
			boolean restrictQualified, boolean inputQualified,
			boolean outputQualified) {
		super(TypeKind.QUALIFIED);
		if (!constQualified && !volatileQualified && !restrictQualified
				&& !inputQualified && !outputQualified)
			throw new RuntimeException("No qualifiers used in qualified type: "
					+ baseType);
		this.baseType = baseType;
		this.constQualified = constQualified;
		this.volatileQualified = volatileQualified;
		this.restrictQualified = restrictQualified;
		this.inputQualified = inputQualified;
		this.outputQualified = outputQualified;
	}

	@Override
	public boolean isConstQualified() {
		return constQualified;
	}

	@Override
	public boolean isVolatileQualified() {
		return this.volatileQualified;
	}

	@Override
	public boolean isRestrictQualified() {
		return this.restrictQualified;
	}

	@Override
	public boolean isInputQualified() {
		return inputQualified;
	}

	@Override
	public boolean isOutputQualified() {
		return outputQualified;
	}

	@Override
	public UnqualifiedObjectType getBaseType() {
		return baseType;
	}

	@Override
	public boolean isComplete() {
		return baseType.isComplete();
	}

	@Override
	public boolean isVariablyModified() {
		return baseType.isVariablyModified();
	}

	@Override
	public int hashCode() {
		int result = 1024 * baseType.hashCode();

		if (constQualified)
			result += 3;
		if (volatileQualified)
			result += 5;
		if (restrictQualified)
			result += 7;
		if (inputQualified)
			result += 11;
		if (outputQualified)
			result += 13;
		return result;
	}

	@Override
	public boolean equals(Object object) {
		if (this == object)
			return true;
		if (object instanceof QualifiedObjectType) {
			QualifiedObjectType that = (QualifiedObjectType) object;

			return constQualified == that.isConstQualified()
					&& volatileQualified == that.isVolatileQualified()
					&& restrictQualified == that.isRestrictQualified()
					&& inputQualified == that.isInputQualified()
					&& outputQualified == that.isOutputQualified()
					&& baseType.equals(that.getBaseType());
		}
		return false;
	}

	@Override
	public void print(String prefix, PrintStream out, boolean abbrv) {
		String seperator = "";

		out.print("QualifiedType[");
		if (inputQualified) {
			out.print(seperator + "_input");
			seperator = ", ";
		}
		if (outputQualified) {
			out.print(seperator + "_output");
			seperator = ", ";
		}
		if (constQualified) {
			out.print(seperator + "const");
			seperator = ", ";
		}
		if (restrictQualified) {
			out.print(seperator + "restrict");
			seperator = ", ";
		}
		if (volatileQualified) {
			out.print(seperator + "volatile");
			seperator = ", ";
		}
		out.println("]");
		out.print(prefix + "| ");
		baseType.print(prefix + "| ", out, true);
	}

	@Override
	public boolean isScalar() {
		return baseType.isScalar();
	}

	@Override
	protected boolean similar(Type other, boolean equivalent,
			Map<TypeKey, Type> seen) {
		if (other instanceof QualifiedObjectType) {
			QualifiedObjectType that = (QualifiedObjectType) other;

			return constQualified == that.isConstQualified()
					&& volatileQualified == that.isVolatileQualified()
					&& restrictQualified == that.isRestrictQualified()
					&& inputQualified == that.isInputQualified()
					&& outputQualified == that.isOutputQualified()
					&& ((CommonType) baseType).similar(that.getBaseType(),
							equivalent, seen);
		}
		return false;
	}

	@Override
	public boolean isConstantQualified() {
		return this.constQualified || this.baseType.isConstantQualified();
	}

}
