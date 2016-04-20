package edu.udel.cis.vsl.civl.model.common.type;

import edu.udel.cis.vsl.civl.model.IF.type.CIVLArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPrimitiveType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * The type for an array of T.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonArrayType extends CommonType implements CIVLArrayType {

	private CIVLType elementType;

	/**
	 * The type for an array of T.
	 * 
	 * @param elementType
	 *            The type of the elements of this array.
	 */
	public CommonArrayType(CIVLType elementType) {
		this.elementType = elementType;
	}

	/**
	 * @return The type of elements in this array.
	 */
	public CIVLType elementType() {
		return elementType;
	}

	@Override
	public String toString() {
		return elementType + "[]";
	}

	@Override
	public boolean isComplete() {
		return false;
	}

	@Override
	public boolean hasState() {
		return elementType.hasState();
	}

	@Override
	public boolean isArrayType() {
		return true;
	}

	@Override
	public SymbolicType getDynamicType(SymbolicUniverse universe) {
		if (dynamicType == null) {
			SymbolicType elementDynamicType = elementType
					.getDynamicType(universe);

			dynamicType = universe.arrayType(elementDynamicType);
			dynamicType = (SymbolicType) universe.canonic(dynamicType);
		}
		return dynamicType;
	}

	@Override
	public boolean isIncompleteArrayType() {
		return true;
	}

	@Override
	public TypeKind typeKind() {
		return TypeKind.ARRAY;
	}

	@Override
	public CIVLType copyAs(CIVLPrimitiveType type, SymbolicUniverse universe) {
		CIVLType newElementType = elementType.copyAs(type, universe);

		if (newElementType.equals(elementType))
			return this;
		return new CommonArrayType(newElementType);
	}

}
