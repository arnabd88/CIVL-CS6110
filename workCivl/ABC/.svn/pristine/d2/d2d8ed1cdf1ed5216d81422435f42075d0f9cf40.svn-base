package edu.udel.cis.vsl.abc.ast.node.IF.declaration;

import edu.udel.cis.vsl.abc.ast.entity.IF.Variable;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;

/**
 * A declaration of a variable ("object").
 * 
 * @author siegel
 * 
 */
public interface VariableDeclarationNode extends OrdinaryDeclarationNode {

	@Override
	Variable getEntity();

	/**
	 * <p>
	 * Does the declaration include the <code>auto</code> storage class
	 * specifier? Default value is <code>false</code>, it can be changed using
	 * {@link #setAutoStorage(boolean)}.
	 * </p>
	 * 
	 * @return <code>true</code> if declaration contains <code>auto</code>
	 * @see #setAutoStorage(boolean)
	 */
	boolean hasAutoStorage();

	/**
	 * Sets the value that will be returned by {@link #hasAutoStorage()}.
	 * 
	 * @param value
	 *            <code>true</code> if declaration contains <code>auto</code>
	 */
	void setAutoStorage(boolean value);

	/**
	 * <p>
	 * Does the declaration include the <code>register</code> storage class
	 * specifier?. Initially <code>false</code>, the value can be changed using
	 * {@link #setRegisterStorage(boolean)}.
	 * </p>
	 * 
	 * <p>
	 * C11 6.9(2): "The storage-class specifiers <code>auto</code> and
	 * <code>register</code> shall not appear in the declaration specifiers in
	 * an external declaration."
	 * </p>
	 * 
	 * <p>
	 * C11 6.7.1(7): "The declaration of an identifier for a function that has
	 * block scope shall have no explicit storage-class specifier other than
	 * <code>extern</code>."
	 * </p>
	 * 
	 * <p>
	 * Since the only remaining kinds of scopes are function prototype and
	 * function, neither of which can contain function declarations, I conclude
	 * that <code>auto</code> and <code>register</code> can never occur in a
	 * function declaration.
	 * </p>
	 * 
	 * <p>
	 * Ergo: this is for objects only, not functions.
	 * </p>
	 * 
	 * @return <code>true</code> iff declaration contains <code>register</code>
	 */
	boolean hasRegisterStorage();

	/**
	 * Sets the value that will be returned by {@link #hasRegisterStorage()}.
	 * 
	 * @param value
	 *            <code>true</code> iff declaration contains
	 *            <code>register</code>
	 */
	void setRegisterStorage(boolean value);

	/**
	 * Does this declaration have shared storage scope? Having shared scope
	 * means that this declaration declares a variable with workgroup scope. It
	 * can be access by threads inside the workgroup, but not outside the
	 * workgroup. Each workgroup has its own copy.
	 * 
	 * @return <code>true</code> iff declaration contains
	 *         <code>__shared__</code>
	 */
	boolean hasSharedStorage();

	/**
	 * Sets the value that will be returned by {@link #hasRSharedStorage()}.
	 * 
	 * @param value
	 *            <code>true</code> iff declaration contains
	 *            <code>register</code>
	 */
	void setSharedStorage(boolean value);

	/**
	 * Gets the (optional) initializer for the object being declared. Returns
	 * <code>null</code> if the declaration does not use an initializer. Default
	 * value is <code>null</code>; it can be changed using
	 * {@link #setInitializer(InitializerNode)}.
	 * 
	 * @return the initializer for the object, or <code>null</code> if no
	 *         initializer is present
	 */
	InitializerNode getInitializer();

	/**
	 * Sets the value that will be returned by {@link #getInitializer()}.
	 * 
	 * @param initializer
	 *            the initializer for the object, or <code>null</code> if no
	 *            initializer is present
	 */
	void setInitializer(InitializerNode initializer);

	/**
	 * Does the declaration include the <code>_Thread_local</code> storage class
	 * specifier? Default value is <code>null</code>; it can be changed using
	 * {@link #setThreadLocalStorage(boolean)}.
	 * 
	 * @return <code>true</code> iff declaration contains
	 *         <code>_Thread_local</code>
	 */
	boolean hasThreadLocalStorage();

	/**
	 * Sets the value that will be returned by {@link #hasThreadLocalStorage()}.
	 * 
	 * @param value
	 *            <code>true</code> iff declaration contains
	 *            <code>_Thread_local</code>
	 */
	void setThreadLocalStorage(boolean value);

	/**
	 * An object declaration may contain any number of alignment specifiers.
	 * These have the form <code>_Alignas ( Type )</code> and
	 * <code>_Alignas ( constant-expression )</code>. This method returns the
	 * types occurring in the first form (if any). Initially <code>null</code>,
	 * this node can be set using
	 * {@link #setTypeAlignmentSpecifiers(SequenceNode)}.
	 * 
	 * @return sequence node of type alignments
	 */
	SequenceNode<TypeNode> typeAlignmentSpecifiers();

	/**
	 * Sets the node that will be returned by {@link #typeAlignmentSpecifiers()}
	 * .
	 * 
	 * @param specifiers
	 *            sequence node of type alignments
	 */
	void setTypeAlignmentSpecifiers(SequenceNode<TypeNode> specifiers);

	/**
	 * An object declaration may contain any number of alignment specifiers.
	 * These have the form <code>_Alignas ( Type )</code> and
	 * <code>_Alignas ( constant-expression )</code>. This method returns the
	 * constant expressions occurring in the second form (if any). Default value
	 * is <code>null</code>, the node can be set using
	 * {@link #setConstantAlignmentSpecifiers(SequenceNode)}.
	 * 
	 * @return sequence node of constant alignments
	 */
	SequenceNode<ExpressionNode> constantAlignmentSpecifiers();

	/**
	 * Sets the node that will be returned by method
	 * {@link #constantAlignmentSpecifiers()}.
	 * 
	 * @param specifiers
	 *            sequence node of constant alignments
	 */
	void setConstantAlignmentSpecifiers(SequenceNode<ExpressionNode> specifiers);

	@Override
	VariableDeclarationNode copy();

	/**
	 * Only used when this {@link VariableDeclarationNode} is used as a
	 * parameter in FORTRAN program. Usually, the type of a parameter in FORTRAN
	 * is call by reference. However, for improving the performance, ABC will
	 * treat <strong>not-modified</strong> parameters as call by value.
	 * 
	 * @return </code>true
	 *         <code>, if this parameter variable is called by reference; <br></code>
	 *         false
	 *         <code>, if it is called by value (or call by reference without being modified).
	 */
	public boolean isRefParameter();

	/**
	 * Sets the boolean field representing the type of this node. <br>
	 * [Only when this node is used as a parameter in a FORTRAN program]
	 * 
	 * @param isRefParameter
	 */
	public void setIsRefParameter(boolean isRefParameter);
}
