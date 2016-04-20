package edu.udel.cis.vsl.abc.ast.conversion.IF;

import edu.udel.cis.vsl.abc.ast.type.IF.StructureOrUnionType;

/**
 * Conversion from one structure or union type to a compatible version of that
 * type.
 * 
 * From C11 Sec. 6.2.7:
 * 
 * <blockquote> Two types have compatible type if their types are the same.
 * Additional rules for determining whether two types are compatible are
 * described in 6.7.2 for type specifiers, in 6.7.3 for type qualifiers, and in
 * 6.7.6 for declarators.55) Moreover, two structure, union, or enumerated types
 * declared in separate translation units are compatible if their tags and
 * members satisfy the following requirements: If one is declared with a tag,
 * the other shall be declared with the same tag. If both are completed anywhere
 * within their respective translation units, then the following additional
 * requirements apply: there shall be a one-to-one correspondence between their
 * members such that each pair of corresponding members are declared with
 * compatible types; if one member of the pair is declared with an alignment
 * specifier, the other is declared with an equivalent alignment specifier; and
 * if one member of the pair is declared with a name, the other is declared with
 * the same name. For two structures, corresponding members shall be declared in
 * the same order. For two structures or unions, corresponding bit-fields shall
 * have the same widths. For two enumerations, corresponding members shall have
 * the same values. </blockquote>
 * 
 * @author siegel
 * 
 */
public interface CompatibleStructureOrUnionConversion extends Conversion {

	@Override
	StructureOrUnionType getOldType();

	@Override
	StructureOrUnionType getNewType();

}
