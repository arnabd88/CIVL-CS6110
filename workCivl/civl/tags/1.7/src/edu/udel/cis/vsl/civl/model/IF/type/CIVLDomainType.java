package edu.udel.cis.vsl.civl.model.IF.type;

import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicUnionType;

/**
 * This is the only one CIVLDomainType associated to the $domain type in
 * program. The dynamic type of this CIVLDomainType is a triple tuple whose
 * components are:
 * <ul>
 * <li>int: dimension</li>
 * <li>int: representation code</li>
 * <li>union: {LiteralDomainType, RectangularDomainType}</li>
 * </ul>
 * 
 * For representation code:
 * <ul>
 * <li>0 stands for RectangularDomainType</li>
 * <li>1 stands for LiteralDomainType</li>
 * </ul>
 * 
 * 
 * 
 */
public interface CIVLDomainType extends CIVLType {
	boolean isComplete();

	/**
	 * Since the domain type has couple more precise sub-types which are all in
	 * one union. This function returns the union type of all sub-types of the
	 * domain type.
	 * 
	 * @param universe
	 * @return
	 */
	SymbolicUnionType getDynamicSubTypesUnion(SymbolicUniverse universe);
}
