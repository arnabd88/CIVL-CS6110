package edu.udel.cis.vsl.civl.state.IF;

import java.io.PrintStream;

import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;

/**
 * A memory unit represents an object or a part of an object that can be
 * accessed through an expression, e.g., a[9].x, b[8], c, etc. A memory unit has
 * three components: dyscope ID, variable ID and reference.
 * 
 * @author Manchun Zheng
 *
 */
public interface MemoryUnit {
	/**
	 * The ID of the dynamic scope of the memory unit.
	 * 
	 * @return
	 */
	int dyscopeID();

	/**
	 * The ID of the variable of the memory unit.
	 * 
	 * @return
	 */
	int varID();

	/**
	 * The reference of the memory unit.
	 * 
	 * @return
	 */
	ReferenceExpression reference();

	void print(PrintStream out);

}
