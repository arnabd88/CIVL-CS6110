package edu.udel.cis.vsl.abc.ast.node.IF.declaration;

import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;

/**
 * <p>
 * A declaration of a variable or function via a C "declarator". In addition to
 * the identifier (common to all declarations), this also specifies a type and
 * storage information.
 * </p>
 * 
 * <p>
 * Note that this is not used to declare members of structures or unions
 * ("fields"). A {@link FieldDeclarationNode} is used for that.
 * </p>
 * 
 * @author siegel
 * 
 */
public interface OrdinaryDeclarationNode extends BlockItemNode,
		DeclarationNode {

	/**
	 * The different kinds of ordinary declarations.
	 * 
	 * @author siegel
	 * 
	 */
	public enum OrdinaryDeclarationKind {
		/**
		 * A declaration of a variable.
		 */
		VARIABLE_DECLARATION,
		/**
		 * A declaration of a function which is not a definition.
		 */
		FUNCTION_DECLARATION,
		/**
		 * A function definition.
		 */
		FUNCTION_DEFINITION,
		/**
		 * A declaration of a CIVL-C abstract function.
		 */
		ABSTRACT_FUNCTION_DEFINITION
	}

	/**
	 * The kind of ordinary declaration this is.
	 * 
	 * @return the ordinary declaration kind
	 */
	OrdinaryDeclarationKind ordinaryDeclarationKind();

	/**
	 * The type of the thing being declared. This may be <code>null</code>:
	 * e.g., in a function declaration, the parameter types do not necessarily
	 * have to be declared.
	 * 
	 * @return the type node for the type of the entity being declared
	 * @see #setTypeNode(TypeNode)
	 */
	TypeNode getTypeNode();

	/**
	 * Sets the type node that will be returned by {@link #getTypeNode()}.
	 * 
	 * @param type
	 *            the node representing the type part of the declaration
	 */
	void setTypeNode(TypeNode type);

	/**
	 * Does the declaration include the <code>extern</code> storage class
	 * specifier? That specifier can be used for functions and objects.
	 * 
	 * @return <code>true</code> iff the declaration contains
	 *         <code>extern</code>
	 * @see #setExternStorage(boolean)
	 */
	boolean hasExternStorage();

	/**
	 * Sets the value that will be returned by {@link #hasExternStorage()}. The
	 * initial default value is <code>false</code>.
	 * 
	 * @param value
	 *            <code>true</code> iff the declaration contains
	 *            <code>extern</code>, else <code>false</code>
	 * @see #hasExternStorage()
	 */
	void setExternStorage(boolean value);

	/**
	 * Does the declaration include the <code>static</code> storage class
	 * specifier? This maybe used for functions and objects.
	 * 
	 * @return <code>true</code> iff declaration contains <code>static</code>
	 * @see #setStaticStorage(boolean)
	 */
	boolean hasStaticStorage();

	/**
	 * Sets the value that will be returned by {@link #hasStaticStorage()}.
	 * Default value is <code>false</code>.
	 * 
	 * @param value
	 *            <code>true</code> iff declaration contains <code>static</code>
	 * @see #hasStaticStorage()
	 */
	void setStaticStorage(boolean value);

	@Override
	OrdinaryDeclarationNode copy();

}
