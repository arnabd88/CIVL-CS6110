package edu.udel.cis.vsl.civl.model.common.type;

import edu.udel.cis.vsl.civl.model.IF.type.ProcessType;

/**
 * The type of a process.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonProcessType implements ProcessType {

	/**
	 * The type of a process.
	 */
	public CommonProcessType() {
	}

	@Override
	public String toString() {
		return "process";
	}
}
