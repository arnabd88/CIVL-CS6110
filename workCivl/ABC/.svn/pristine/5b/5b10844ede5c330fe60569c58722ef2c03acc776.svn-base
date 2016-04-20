package edu.udel.cis.vsl.abc.ast.node.IF.declaration;

import edu.udel.cis.vsl.abc.ast.entity.IF.Entity;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;

/**
 * <p>
 * The root of the declaration node type hierarchy. According to C11, "A
 * declaration specifies the interpretation and attributes of a set of
 * identifiers." An object of this type specifies a declaration for exactly one
 * identifier.
 * </p>
 * 
 * <p>
 * A DeclarationNode does not correspond exactly to the notion of "declaration"
 * in the C Standard. For example, in the C Standard, a static assertion is a
 * kind of declaration. This seems more like a grammatical convenience (since a
 * static assertion can appear almost anywhere a declaration can) than a logical
 * organization of the concepts, as a static assertion does not specify
 * "the interpretation and attributes of a set of identifiers".
 * </p>
 * 
 * <p>
 * Every declaration node has at least one child: an identifier node for the
 * identifier being declared. It is possible for that identifier node to be
 * <code>null</code>, for example, in an anonymous <code>struct</code> or
 * <code>enum</code>.
 * </p>
 * 
 * <p>
 * Furthermore, every declaration node declares some abstract thing, called an
 * {@link Entity}. This class provides a method to get and set that entity.
 * </p>
 * 
 * @see Entity
 * 
 * @author siegel
 * 
 */
public interface DeclarationNode extends ASTNode {

	/**
	 * Gets the identifier node which contains the name of the entity being
	 * declared. May be <code>null</code>.
	 * 
	 * @return the identifier for the name of the entity being declared
	 */
	IdentifierNode getIdentifier();

	/**
	 * The name of the identifier being declared as a string. Could be
	 * <code>null</code>. If the identifier is not <code>null</code>, this
	 * method returns the same string returned by
	 * <code>getIdentifier().name()</code>. It is provided for convenience.
	 * 
	 * @return name of identifier being declared, or <code>null</code> if the
	 *         declaration is anonymous
	 */
	String getName();

	/**
	 * Sets the identifier node.
	 * 
	 * @param identifier
	 *            the identifier node
	 */
	void setIdentifier(IdentifierNode identifier);

	/**
	 * Is this the defining declaration of the identifier? According to C11, "A
	 * definition of an identifier is a declaration for that identifier that: -
	 * for an object, causes storage to be reserved for that object; - for a
	 * function, includes the function body; - for an enumeration constant, is
	 * the (only) declaration of the identifier; - for a typedef name, is the
	 * first (or only) declaration of the identifier."
	 * 
	 * @return <code>true</code> iff this is the identifier's definition.
	 * @see #setIsDefinition(boolean)
	 */
	boolean isDefinition();

	/**
	 * Sets the "isDefinition" field to the given boolean value.
	 * 
	 * @param value
	 *            new value for "isDefinition"
	 * @see #isDefinition()
	 */
	void setIsDefinition(boolean value);

	/**
	 * Returns the entity whose existence is declared by this declaration. This
	 * is initially <code>null</code>, and can be changed by
	 * {@link #setEntity(Entity)}.
	 * 
	 * @return the entity declared by this declaration
	 * @see #setEntity(Entity)
	 */
	Entity getEntity();

	/**
	 * Sets the entity associated to this declaration.
	 * 
	 * @param entity
	 *            the entity to associate to this node
	 * @see #getEntity()
	 */
	void setEntity(Entity entity);

	@Override
	DeclarationNode copy();
}
