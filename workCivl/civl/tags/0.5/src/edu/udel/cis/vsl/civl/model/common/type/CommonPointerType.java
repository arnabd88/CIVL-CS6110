/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.type;

import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPointerType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * 
 * @author zirkel
 * 
 */
public class CommonPointerType extends CommonType implements CIVLPointerType {

	private CIVLType baseType;

	public CommonPointerType(CIVLType baseType, SymbolicType pointerType) {
		super();
		this.dynamicType = pointerType;
		this.baseType = baseType;
	}

	@Override
	public CIVLType baseType() {
		return baseType;
	}

	@Override
	public String toString() {
		return baseType + "*";
	}

	@Override
	public boolean isPointerType() {
		return true;
	}

	@Override
	public Scope getRegion() {
		return null;
	}

	@Override
	public boolean hasState() {
		return false;
	}

	@Override
	public SymbolicType getDynamicType(SymbolicUniverse universe) {
		return dynamicType;
	}

}
