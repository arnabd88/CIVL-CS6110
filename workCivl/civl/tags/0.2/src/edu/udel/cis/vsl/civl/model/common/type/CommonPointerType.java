/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.type;

import edu.udel.cis.vsl.civl.model.IF.type.PointerType;
import edu.udel.cis.vsl.civl.model.IF.type.Type;

/**
 * @author zirkel
 *
 */
public class CommonPointerType implements PointerType {

	private Type baseType;
	
	public CommonPointerType(Type baseType) {
		this.baseType = baseType;
	}
	
	/* (non-Javadoc)
	 * @see edu.udel.cis.vsl.civl.model.IF.type.PointerType#baseType()
	 */
	@Override
	public Type baseType() {
		return baseType;
	}
	
	@Override
	public String toString() {
		return baseType + "*";
	}

}
