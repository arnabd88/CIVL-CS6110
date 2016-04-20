package edu.udel.cis.vsl.civl.state.IF;

import java.io.PrintStream;

/**
 * A memory unit set represents a set of memory units.
 * 
 * @author Manchun Zheng
 *
 */
public interface MemoryUnitSet {
	/**
	 * Gets the memory units of this set.
	 * 
	 * @return
	 */
	Iterable<MemoryUnit> memoryUnits();

	void print(PrintStream out);

	void add(MemoryUnit mu);

}
