package edu.udel.cis.vsl.abc.ast.entity.IF;

import edu.udel.cis.vsl.abc.ast.node.IF.declaration.DeclarationNode;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.front.common.astgen.PragmaHandler;

public interface ProgramEntity extends Entity {

	/**
	 * The different kinds of linkage an entity may have: external, internal, or
	 * none. Roughly speaking, an entity with external linkage refers to a thing
	 * which may lie outside of the translation union; one with internal linkage
	 * refers to a single thing which lies in the translation unit but may be
	 * declared in multiple scopes; something with no linkage can only be
	 * declared in the one scope where it resides.
	 */
	public static enum LinkageKind {
		EXTERNAL, INTERNAL, NONE
	}

	/**
	 * Returns an iterator over all the known delcarations of this entity. An
	 * entity may be declared multiple times. This includes the definition.
	 * 
	 * @return iterator over declarations of this entity
	 */
	Iterable<DeclarationNode> getDeclarations();

	/**
	 * Gets one of the declarations of this entity.
	 * 
	 * @return a declaration of this entity or <code>null</code> if there aren't
	 *         any
	 */
	DeclarationNode getFirstDeclaration();

	/**
	 * Returns the number of declarations of this entity.
	 * 
	 * @return the number of declarations of this entity
	 */
	int getNumDeclarations();

	/**
	 * Returns the index-th declaration of this entity.
	 * 
	 * @param index
	 *            an integer in the range [0,n), where n is the number of
	 *            declarations of this entity
	 * @return the index-th declaration of this entity
	 */
	DeclarationNode getDeclaration(int index);

	/**
	 * Adds a declaration to this entity.
	 * 
	 * @param declaration
	 *            a declaration of this entity
	 */
	void addDeclaration(DeclarationNode declaration);

	/**
	 * <p>
	 * Gets the definition, i.e., the defining declaration of this entity. Every
	 * entity has at most one definition. The definition is a declaration of a
	 * special kind. For example, for an object (variable), a definition is the
	 * declaration that allocates storage for that object. For a function, a
	 * definition is the declaration the contains the function body.
	 * </p>
	 * 
	 * <p>
	 * The definition is initially <code>null</code>, but can be set using
	 * method {@link #setDefinition(DeclarationNode)}.
	 * </p>
	 * 
	 * @return the definition of this entity or <code>null</code>
	 */
	DeclarationNode getDefinition();

	/**
	 * <p>
	 * Sets the definition for this entity. Every entity has at most one
	 * definition. The definition is a declaration of a special kind. For
	 * example, for an object (variable), a definition is the declaration that
	 * allocates storage for that object. For a function, a definition is the
	 * declaration the contains the function body.
	 * </p>
	 * 
	 * <p>
	 * The definition is initially <code>null</code>, and can be set using this
	 * method. Note that this does not affect the list of declarations of this
	 * entity. It is the client's responsibility to add the definition to the
	 * list of declarations as well as to invoke this method, to ensure that the
	 * definition occurs in the list of declarations.
	 * </p>
	 * 
	 * @param declaration
	 *            the declaration node for the definition
	 */
	void setDefinition(DeclarationNode declaration);

	/**
	 * Returns the kind of linkage this entity has.
	 * 
	 * @return the kind of linkage this entity has
	 */
	ProgramEntity.LinkageKind getLinkage();

	/**
	 * Sets the linkage of this entity. It is initially {@link LinkageKind#NONE}
	 * .
	 * 
	 * @param linkage
	 *            the linkage kind of this entity
	 */
	void setLinkage(ProgramEntity.LinkageKind linkage);

	/**
	 * <p>
	 * Other than {@link Label}, and {@link PragmaHandler}, every kind of Entity
	 * has a type, returned by this method. For a {@link Label} or
	 * {@link PragmaHandler}, this returns <code>null</code>.
	 * </p>
	 * 
	 * <p>
	 * The type is initially <code>null</code>. It can be set using method
	 * {@link #setType(Type)}.
	 * </p>
	 * 
	 * @return the type of this entity or <code>null</code>
	 */
	Type getType();

	/**
	 * Sets the type of this entity.
	 * 
	 * @param type
	 *            the type of this entity
	 */
	void setType(Type type);

	/**
	 * Is this a system-defined entity (as opposed to a user-defined one)?
	 * Examples include standard types, like <code>size_t</code>. The default is
	 * false; it can be changed using method {@link #setIsSystem(boolean)}.
	 */
	boolean isSystem();

	/**
	 * Declares that this entity is or is not a system-defined entity.
	 * 
	 * @param value
	 *            if <code>true</code>, declares this to be a system-defined
	 *            entity; if <code>false</code>, declares this to be a
	 *            user-defined entity. The default is <code>false</code>.
	 */
	void setIsSystem(boolean value);

}
