package edu.udel.cis.vsl.abc.ast.type.IF;

import edu.udel.cis.vsl.abc.ast.entity.IF.Entity;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FieldDeclarationNode;
import edu.udel.cis.vsl.abc.ast.value.IF.Value;

/**
 * A Field is a member of a structure or union. A Field is determined by the
 * following (1) its name, which is obtained by method {@link #getName()} in the
 * parent interface {@link Entity}, (2) its type, which must be an object type,
 * and is obtained by method {@link #getType()}, and (3) its optional bit width,
 * obtained by method {@link #getBitWidth()}. Note that any of these 3 things
 * may be <code>null</code> (but not all three) in an instance.
 * 
 * @author siegel
 * 
 */
public interface Field extends Entity {

	/**
	 * Returns the index of this field in the list of members of the structure
	 * or union. Members are indexed starting from 0.
	 * 
	 * @return field index in structure or union
	 */
	int getMemberIndex();

	/**
	 * Returns the (sole) declaration of this field in the AST.
	 * 
	 * @return the sole declaration of this field
	 */
	FieldDeclarationNode getDefinition();

	/**
	 * Returns the type of the field, or <code>null</code> if no type is
	 * specified. A field with a non-<code>null</code> type must have an object
	 * type.
	 * 
	 * @return the type of the field
	 */
	ObjectType getType();

	/**
	 * Returns the integer bit width constant value, or <code>null</code> if a
	 * bit width is not specified.
	 * 
	 * @return bit width or <code>null</code>
	 */
	Value getBitWidth();

}
