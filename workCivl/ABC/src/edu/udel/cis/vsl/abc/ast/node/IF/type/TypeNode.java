package edu.udel.cis.vsl.abc.ast.node.IF.type;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.SizeableNode;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;

public interface TypeNode extends SizeableNode {

	/**
	 * The different kinds of type names.
	 */
	public static enum TypeNodeKind {
		ARRAY, ATOMIC, BASIC, DOMAIN, ENUMERATION, FUNCTION, POINTER, RANGE, SCOPE, STRUCTURE_OR_UNION, TYPEDEF_NAME, VOID,
		/**
		 * typeof() of GNU C extension
		 */
		TYPEOF
	};

	@Override
	TypeNode copy();

	/**
	 * Returns the conceptual C type associated to this type node.
	 * 
	 * @return the C type defined by this type node
	 */
	Type getType();

	/**
	 * Is this an "_Atomic" qualified type?
	 * 
	 * @return true iff this is an "_Atomic" qualified type
	 */
	boolean isAtomicQualified();

	/**
	 * Is this a "const" qualified type?
	 * 
	 * @return true iff this is a const qualified type.
	 */
	boolean isConstQualified();

	/**
	 * Is the CIVL-C type qualifier <code>$input</code> used?
	 * 
	 * @return <code>true</code> if this type is <code>$input</code>-qualified
	 */
	boolean isInputQualified();

	boolean isOutputQualified();

	/**
	 * Is this a "restrict" qualified type?
	 * 
	 * @return true iff this is a "restrict" qualified type.
	 */
	boolean isRestrictQualified();

	/**
	 * Is this a "volatile" qualified type?
	 * 
	 * @return true iff this is a volatile qualified type.
	 */
	boolean isVolatileQualified();

	/**
	 * The kind of type name this is. See definition of the enumerated type
	 * TypeNameKind. These kinds partition the set of all type names.
	 * 
	 * If the kind is BASIC, this object can be safely cast to BasicType.
	 * 
	 * If the kind is DOMAIN, the object can be safely cast to DomainType.
	 * 
	 * If the kind is ENUMERATION, this object can be safely cast to
	 * EnumerationType.
	 * 
	 * If the kind is ARRAY, this object can be safely cast to ArrayType.
	 * 
	 * If the kind is STRUCTURE_OR_UNION, this object can be safely cast to
	 * StructureOrUnionType.
	 * 
	 * If the kind is FUNCTION, this object can be safely cast to FunctionType.
	 * 
	 * If the kind is POINTER, this object can be safely cast to PointerType.
	 * 
	 * If the kind is ATOMIC, this object can be safely cast to AtomicType.
	 * 
	 * @return the kind of this type
	 */
	TypeNodeKind kind();

	void setAtomicQualified(boolean value);

	void setConstQualified(boolean value);

	void setInputQualified(boolean value);

	void setOutputQualified(boolean value);

	void setRestrictQualified(boolean value);

	/**
	 * Sets the type that will be returned by subsequent calls to getType().
	 * 
	 * @param type
	 *            the type to associate to this node
	 */
	void setType(Type type);

	void setVolatileQualified(boolean value);

	/**
	 * 
	 * @return The kind of this type node.
	 */
	TypeNodeKind typeNodeKind();

}
