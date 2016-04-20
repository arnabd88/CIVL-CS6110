package edu.udel.cis.vsl.civl.model.IF.type;

import java.math.BigInteger;

/**
 * An enumeration type.
 * 
 * @author Manchun Zheng
 * 
 */
public interface CIVLEnumType extends CIVLType {
	/**
	 * Gets the name of the enumeration type.
	 * 
	 * @return
	 */
	String name();

	/**
	 * Gets the value of a certain enumerator (member) of the enumeration type.
	 * 
	 * @param member
	 *            The name of the member.
	 * @return The value of the enumerator.
	 */
	BigInteger valueOf(String member);
	
	BigInteger firstValue();
}
