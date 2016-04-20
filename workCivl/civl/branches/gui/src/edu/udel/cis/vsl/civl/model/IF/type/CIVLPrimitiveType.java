package edu.udel.cis.vsl.civl.model.IF.type;

import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * A primitive type is a type of which there is only one instance. In addition,
 * there is a single symbolic type corresponding to each primitive type.
 * 
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface CIVLPrimitiveType extends CIVLType {

	public enum PrimitiveTypeKind {
		BOOL, DYNAMIC, INT, PROCESS, REAL, SCOPE, VOID, CHAR, MEMORY
	};

	/**
	 * @return The kind of this primitive type, an element of the enumerated
	 *         type
	 */
	PrimitiveTypeKind primitiveTypeKind();

	/**
	 * Returns the symbolic value representing the size of this primitive type,
	 * i.e., the value of "sizeof(t)".
	 * 
	 * @return the size of this type
	 */
	NumericExpression getSizeof();

	/**
	 * Returns facts about this primitive type that should be added to the path
	 * condition whenever it is used. For example, that "sizeof(t)>0".
	 * 
	 * @return predicate which must hold concerning this type
	 */
	BooleanExpression getFacts();

	SymbolicExpression initialValue(SymbolicUniverse universe);

}
