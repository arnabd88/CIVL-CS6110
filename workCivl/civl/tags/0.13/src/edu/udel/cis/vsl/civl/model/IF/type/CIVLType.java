package edu.udel.cis.vsl.civl.model.IF.type;

import edu.udel.cis.vsl.civl.model.IF.type.CIVLPrimitiveType.PrimitiveTypeKind;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * Parent of all types.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface CIVLType {

	public enum TypeKind {
		ARRAY, COMPLETE_ARRAY, BUNDLE, DOMAIN, ENUM, POINTER, PRIMITIVE, STRUCT_OR_UNION, FUNCTION, HEAP
	}

	TypeKind typeKind();

	/**
	 * If this type contains any array with non-constant extent, it "has state"
	 * in the sense that the dynamic type may depend on the state.
	 * 
	 * @return true iff type contains array with non-constant extent
	 */
	boolean hasState();

	/**
	 * If a type is defined using a struct, union, or typedef, and it contains
	 * state, it may have to be evaluated and stored in a variable of type
	 * CIVLDynamicType. For such a type, this method returns the corresponding
	 * variable. For other types, it returns null.
	 * 
	 * @return the state variable associated to this type or null
	 */
	Variable getStateVariable();

	/**
	 * Sets this type's state variable to the given variable
	 * 
	 * @param variable
	 *            a variable of type CIVLDynamicType used to store the dynamic
	 *            type resulting from evaluating this type in a state
	 */
	void setStateVariable(Variable variable);

	/**
	 * This returns the dynamic type corresponding to this static type in which
	 * all array extent expressions are ignored, i.e., all of the dynamic array
	 * types are incomplete. May be null (only in the case of the primitive type
	 * of kind {@link PrimitiveTypeKind.VOID}).
	 * 
	 * @return the dynamic type corresponding to this static type with
	 *         incomplete array type
	 */
	SymbolicType getDynamicType(SymbolicUniverse universe);

	/**
	 * All dynamic types occurring in a model are indexed. This returns the
	 * index of the dynamic type corresponding to this type.
	 * 
	 * @return the dynamic type index
	 */
	int getDynamicTypeIndex();

	/**
	 * 
	 * @return true iff this type is numeric
	 */
	boolean isNumericType();

	/**
	 * 
	 * @return true iff this type is integer type
	 */
	boolean isIntegerType();

	/**
	 * 
	 * @return true iff this type is real type
	 */
	boolean isRealType();

	/**
	 * 
	 * @return true iff this type is pointer type
	 */
	boolean isPointerType();

	/**
	 * 
	 * @return true iff this type is process type
	 */
	boolean isProcessType();

	/**
	 * 
	 * @return true iff this type is scope type
	 */
	boolean isScopeType();

	/**
	 * 
	 * @return true iff this type is void type
	 */
	boolean isVoidType();

	/**
	 * 
	 * @return true iff this type is heap type
	 */
	boolean isHeapType();

	/**
	 * 
	 * @return true iff this type is bundle type
	 */
	boolean isBundleType();

	/**
	 * 
	 * @return true iff this type is struct type
	 */
	boolean isStructType();

	/**
	 * 
	 * @return true iff this type is union type
	 */
	boolean isUnionType();

	/**
	 * 
	 * @return true iff this type is array type
	 */
	boolean isArrayType();

	boolean isIncompleteArrayType();

	/**
	 * 
	 * @return true iff this type is char type
	 */
	boolean isCharType();

	/**
	 * 
	 * @return true iff this type is a handle type (e.g., $gcomm, $heap, etc)
	 */
	boolean isHandleType();

	/**
	 * 
	 * @return true iff this type is the object type of some handle type.
	 */
	boolean isHandleObjectType();

	/**
	 * 
	 * @return true iff this type is an enumeration type.
	 */
	boolean isEnumerationType();

	/**
	 * 
	 * 
	 * @return true iff this type is a boolean type.
	 */
	boolean isBoolType();

	boolean isDomainType();

	CIVLType copyAs(CIVLPrimitiveType type, SymbolicUniverse universe);
}
