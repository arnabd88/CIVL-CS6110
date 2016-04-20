/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.type;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression.ExpressionKind;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLCompleteArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPrimitiveType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;

/**
 * @author zirkel
 * 
 */
public class CommonCompleteArrayType extends CommonArrayType implements
		CIVLCompleteArrayType {

	private Expression extent;

	/**
	 * @param baseType
	 */
	public CommonCompleteArrayType(CIVLType baseType, Expression extent) {
		super(baseType);
		this.extent = extent;
	}

	@Override
	public Expression extent() {
		return extent;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj instanceof CIVLCompleteArrayType) {
			CIVLCompleteArrayType that = (CIVLCompleteArrayType) obj;

			return this.elementType().equals(that.elementType())
					&& this.extent.equals(that.extent());
		}
		return false;
	}

	@Override
	public boolean isComplete() {
		return true;
	}

	@Override
	public boolean hasState() {
		if (super.hasState())
			return true;
		return extent.expressionKind() != ExpressionKind.INTEGER_LITERAL;
	}

	public String toString() {
		return elementType() + "[" + extent() + "]";
	}

	@Override
	public TypeKind typeKind() {
		return TypeKind.COMPLETE_ARRAY;
	}

	@Override
	public CIVLType copyAs(CIVLPrimitiveType type, SymbolicUniverse universe) {
		CIVLType newElementType = this.elementType().copyAs(type, universe);

		if (newElementType.equals(this.elementType()))
			return this;
		return new CommonCompleteArrayType(newElementType, extent);
	}
}
