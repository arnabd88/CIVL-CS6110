package edu.udel.cis.vsl.abc.ast.conversion.IF;

import edu.udel.cis.vsl.abc.ast.type.IF.MemoryType;

/**
 * convert any lhs expression into a memory expression, only used for contracts
 * 
 * @author Manchun Zheng
 *
 */
public interface MemoryConversion extends Conversion {
	@Override
	MemoryType getNewType();
}
