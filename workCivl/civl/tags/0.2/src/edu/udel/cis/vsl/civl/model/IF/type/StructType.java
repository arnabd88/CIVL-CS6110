package edu.udel.cis.vsl.civl.model.IF.type;

import java.util.List;

import edu.udel.cis.vsl.civl.model.IF.Identifier;

public interface StructType extends Type {

	/**
	 * 
	 * @return A list of the field types in this struct.
	 */
	List<StructField> fields();
	
	/**
	 * @return The name of this struct.
	 */
	Identifier name();
}
