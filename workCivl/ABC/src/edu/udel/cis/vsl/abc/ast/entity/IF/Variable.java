package edu.udel.cis.vsl.abc.ast.entity.IF;

import java.util.Iterator;

import edu.udel.cis.vsl.abc.ast.node.IF.declaration.InitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.type.IF.ObjectType;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.ast.value.IF.Value;

/**
 * A variable ("object") entity.
 * 
 * @author siegel
 * 
 */
public interface Variable extends OrdinaryEntity {

	/**
	 * An enumerated type for the four different kinds of "storage duration"
	 * defined in the C11 Standard.
	 * 
	 * @author siegel
	 * 
	 */
	public static enum StorageDurationKind {
		STATIC, THREAD, AUTOMATIC, ALLOCATED
	};

	/**
	 * Gets the storage duration associated to this variable.
	 * 
	 * @return the storage duration
	 */
	StorageDurationKind getStorageDuration();

	/**
	 * Sets the storage duration assocaited to this variable.
	 * 
	 * @param duration
	 *            the storage duration
	 */
	void setStorageDuration(StorageDurationKind duration);

	/**
	 * Gets the (optional) initializer for the object being declared.
	 * 
	 * @return the initializer for the new object, or <code>null</code> if no
	 *         initializer is present
	 */
	InitializerNode getInitializer();

	/**
	 * Sets the initializer for this variable.
	 * 
	 * @param initializer
	 *            node representing an initializer
	 */
	void setInitializer(InitializerNode initializer);

	/**
	 * An object declaration may contain any number of alignment specifiers.
	 * These have the form <code>_Alignas ( Type )</code> and
	 * <code>_Alignas ( constant-expression )</code>. This method returns the
	 * types occurring in the first form (if any). This list is initially empty;
	 * types can be added to it using the method {@link #addTypeAlignment(Type)}
	 * 
	 * @return the type alignments
	 */
	Iterator<Type> getTypeAlignments();

	/**
	 * Adds an alignment type to the list of type alignments associated to this
	 * node.
	 * 
	 * @param type
	 *            a type
	 * @see #getTypeAlignments()
	 */
	void addTypeAlignment(Type type);

	/**
	 * An object declaration may contain any number of alignment specifiers.
	 * These have the form <code>_Alignas ( Type )</code> and
	 * <code>_Alignas ( constant-expression )</code>. This method returns the
	 * constant expressions occurring in the second form (if any). The list of
	 * constant alignments is initially empty; constants are added to the list
	 * using method {@link #addConstantAlignment(Value)}.
	 * 
	 * @return constant alignments
	 */
	Iterator<Value> getConstantAlignments();

	/**
	 * Adds a constant to the list of alignment constants assocaited to this
	 * variable.
	 * 
	 * @param constant
	 *            an integer constant
	 * @see #getConstantAlignments()
	 */
	void addConstantAlignment(Value constant);

	@Override
	VariableDeclarationNode getDefinition();

	@Override
	ObjectType getType();

	@Override
	VariableDeclarationNode getDeclaration(int index);
}
