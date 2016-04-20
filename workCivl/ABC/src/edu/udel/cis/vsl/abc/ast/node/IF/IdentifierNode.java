package edu.udel.cis.vsl.abc.ast.node.IF;

import edu.udel.cis.vsl.abc.ast.entity.IF.Entity;

/**
 * An identifier can denote: (1) an object, (2) a function, (3) a tag of a
 * structure, union, or enumeration, (4) a member of a structure, union, or
 * enumeration, (5) a typedef name, or (6) a label name. All of these things are
 * called "entities".
 * 
 * An identifier node represents any occurrence of an identifier in a program.
 * 
 * @see Entity
 * 
 * @author siegel
 * 
 */
public interface IdentifierNode extends ASTNode {

	/**
	 * Returns the name of this identifier node. This is a non-null string. This
	 * is typically the string that actually appears in the source code.
	 * 
	 * @return the name of this identifier
	 */
	String name();

	/**
	 * Sets the name of this identifier.
	 * 
	 * @param name
	 *            new value for identifier name
	 */
	void setName(String name);

	/**
	 * Returns the entity to which this identifier refers. Every identifier
	 * refers to some entity: a variable, function, structure or union, typedef,
	 * enumeration, etc. All of those things are examples if entities.
	 * 
	 * Typically, the entity starts off as null, and is set during the standard
	 * analysis phase.
	 * 
	 * The information provided by the getEntity methods in the AST is what is
	 * typically referred to as the "symbol table".
	 * 
	 * @return the entity to which this identifier refers, or <code>null</code>
	 *         if that information has not yet been computed
	 */
	Entity getEntity();

	/**
	 * Sets the entity to which this identifier refers. This method is typically
	 * called by the standard analysis routine, which computes this
	 * "symbol table" information.
	 * 
	 * @param entity
	 *            the entity to which this identifier refers; must be non-null
	 */
	void setEntity(Entity entity);

	@Override
	IdentifierNode copy();

}
