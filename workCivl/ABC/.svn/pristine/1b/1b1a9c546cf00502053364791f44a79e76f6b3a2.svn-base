package edu.udel.cis.vsl.abc.ast.type.common;

import java.io.PrintStream;
import java.util.Map;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.type.IF.ArrayType;
import edu.udel.cis.vsl.abc.ast.type.IF.ObjectType;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.ast.value.IF.IntegerValue;

public class CommonArrayType extends CommonObjectType implements ArrayType {

	private final static int classCode = CommonArrayType.class.hashCode();

	private ObjectType elementType;

	private ExpressionNode variableSize;

	private IntegerValue constantSize;

	private boolean unspecifiedVariableLength;

	/**
	 * Creates a new array type with given element type and value for
	 * unspecifiedVariableLength.
	 * 
	 * @param elementType
	 *            a complete object type
	 * @param unspecifiedVariableLength
	 *            is this an array declared with "*" for the size expression?
	 */
	public CommonArrayType(ObjectType elementType,
			boolean unspecifiedVariableLength) {
		super(TypeKind.ARRAY);
		this.elementType = elementType;
		this.variableSize = null;
		this.constantSize = null;
		this.unspecifiedVariableLength = unspecifiedVariableLength;
	}

	/**
	 * Creates a new complete array type in which the extent does not have a
	 * constant value.
	 * 
	 * @param elementType
	 *            a complete object type
	 * @param variableSize
	 *            the expression specifying the length of the array
	 */
	public CommonArrayType(ObjectType elementType, ExpressionNode variableSize) {
		super(TypeKind.ARRAY);
		this.elementType = elementType;
		this.variableSize = variableSize;
		this.constantSize = null;
		this.unspecifiedVariableLength = false;
	}

	/**
	 * Creates a new complete array type in which the extent has a known
	 * constant value.
	 * 
	 * @param elementType
	 *            complete object type
	 * @param constantSize
	 *            the constant obtained by evaluating the extent expression
	 */
	public CommonArrayType(ObjectType elementType, IntegerValue constantSize) {
		super(TypeKind.ARRAY);
		this.elementType = elementType;
		this.variableSize = null;
		this.constantSize = constantSize;
		this.unspecifiedVariableLength = false;
	}

	@Override
	public boolean isComplete() {
		return variableSize != null || constantSize != null
				|| unspecifiedVariableLength;
	}

	@Override
	public ObjectType getElementType() {
		return elementType;
	}

	@Override
	public ExpressionNode getVariableSize() {
		return variableSize;
	}

	@Override
	public boolean isVariableLengthArrayType() {
		return unspecifiedVariableLength || variableSize != null
				|| !elementType.hasKnownConstantSize();
	}

	@Override
	public boolean hasUnspecifiedVariableLength() {
		return this.unspecifiedVariableLength;
	}

	@Override
	public boolean isVariablyModified() {
		return isVariableLengthArrayType() || elementType.isVariablyModified();
	}

	@Override
	public IntegerValue getConstantSize() {
		return constantSize;
	}

	@Override
	public int hashCode() {
		int result = classCode ^ ((CommonType) elementType).hashCode();

		if (constantSize != null)
			result ^= constantSize.hashCode();
		else if (variableSize != null)
			result ^= variableSize.hashCode();
		if (unspecifiedVariableLength)
			result ^= 172830823; // random int
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof CommonArrayType) {
			CommonArrayType that = (CommonArrayType) obj;

			if (!elementType.equals(that.elementType))
				return false;
			if (constantSize != null) {
				if (that.constantSize == null)
					return false;
				if (!constantSize.equals(that.constantSize))
					return false;
			} else {
				if (that.constantSize != null)
					return false;
				if (variableSize != null) {
					if (that.variableSize == null)
						return false;
					if (!variableSize.equals(that.variableSize))
						return false;
				} else {
					if (that.variableSize != null)
						return false;
				}
			}
			return unspecifiedVariableLength == that.unspecifiedVariableLength;
		}
		return false;
	}

	private boolean equivalentTo(Type other, Map<TypeKey, Type> seen) {
		if (other instanceof CommonArrayType) {
			CommonArrayType that = (CommonArrayType) other;

			if (!((CommonType) elementType).similar(that.elementType, true,
					seen))
				return false;
			if (constantSize != null) {
				if (that.constantSize == null)
					return false;
				if (!constantSize.equals(that.constantSize))
					return false;
			} else {
				if (that.constantSize != null)
					return false;
				if (variableSize != null) {
					if (that.variableSize == null)
						return false;
					if (!variableSize.equals(that.variableSize))
						return false;
				} else {
					if (that.variableSize != null)
						return false;
				}
			}
			return unspecifiedVariableLength == that.unspecifiedVariableLength;
		}
		return false;
	}

	private boolean compatibleWith(Type type, Map<TypeKey, Type> seen) {
		if (type instanceof CommonArrayType) {
			CommonArrayType that = (CommonArrayType) type;

			if (!((CommonType) elementType).similar(that.elementType, false,
					seen))
				return false;
			if (constantSize != null && that.constantSize != null
					&& !constantSize.equals(that.constantSize))
				return false;
			return true;
		}
		return false;
	}

	@Override
	public String toString() {
		String result = "ArrayType[elementType=" + elementType;

		if (variableSize != null)
			result += ", size=" + variableSize;
		if (constantSize != null)
			result += ", size=" + constantSize;
		if (unspecifiedVariableLength)
			result += ", unspecifiedVariableLength";
		result += "]";
		return result;
	}

	@Override
	public void print(String prefix, PrintStream out, boolean abbrv) {
		out.println("Array");
		out.print(prefix + "| elementType = ");
		elementType.print(prefix + "| ", out, true);
		out.println();
		out.print(prefix + "| size = ");
		if (constantSize != null)
			out.print(constantSize);
		else if (variableSize != null)
			out.print(variableSize);
		else if (unspecifiedVariableLength)
			out.print("unspecified variable length");
	}

	@Override
	public boolean isScalar() {
		return false;
	}

	@Override
	protected boolean similar(Type other, boolean equivalent,
			Map<TypeKey, Type> seen) {
		return equivalent ? equivalentTo(other, seen) : compatibleWith(other,
				seen);
	}

	@Override
	public boolean isConstantQualified() {
		return this.elementType.isConstantQualified();
	}
}
