package edu.udel.cis.vsl.civl.model.IF.type;

import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;

/**
 * A field in a struct has a name and a type.
 * 
 * @author zirkel
 * 
 */
public interface StructOrUnionField {

	Identifier name();

	CIVLType type();

	int index();

	StructOrUnionField copyAs(CIVLPrimitiveType type, SymbolicUniverse universe);
}
