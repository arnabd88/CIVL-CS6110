package edu.udel.cis.vsl.abc.ast.entity.IF;

import java.util.Iterator;
import java.util.Set;

import edu.udel.cis.vsl.abc.ast.node.IF.acsl.ContractNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.type.IF.FunctionType;

/**
 * A function is an entity which takes inputs, executes a statement, and
 * possibly returns a result.
 * 
 * @author siegel
 * 
 */
public interface Function extends OrdinaryEntity {

	@Override
	FunctionType getType();

	/**
	 * Is the function declared with the <code>inline</code> specifier,
	 * indicating that this is an inline function?
	 * 
	 * @return <code>true</code> iff the function is an inline function
	 */
	boolean isInlined();

	/**
	 * Sets whether this function is an inline function
	 * 
	 * @param value
	 *            <code>true</code> if inlined, <code>false</code> if not
	 */
	void setIsInlined(boolean value);

	/**
	 * Is the function declared with the <code>$atomic_f</code> specifier,
	 * indicating that this is an atomic function?
	 * 
	 * @return <code>true</code> iff the function is an atomic function
	 */
	boolean isAtomic();

	/**
	 * Sets whether this function is an atomic function
	 * 
	 * @param value
	 *            <code>true</code> if atomic, <code>false</code> if not
	 */
	void setAtomic(boolean value);

	/**
	 * Is the function declared with the <code>$system</code> specifier,
	 * indicating that this is a system function?
	 * 
	 * @return <code>true</code> iff the function is a system function
	 */
	boolean isSystemFunction();

	/**
	 * Sets whether this function is a system function
	 * 
	 * @param value
	 *            <code>true</code> if this is a system function,
	 *            <code>false</code> if not
	 */
	void setSystemFunction(boolean value);

	/**
	 * Is the function declared with the <code>_Noreturn</code> specifier,
	 * indicating that the function does not return.
	 * 
	 * @return <code>true</code> iff the function is declared with
	 *         <code>_Noreturn</code>
	 */
	boolean doesNotReturn();

	/**
	 * Sets whether this function is declared with <code>_Noreturn</code>.
	 * 
	 * @param value
	 *            <code>true</code> if <code>_Noreturn</code>,
	 *            <code>false</code> if not
	 */
	void setDoesNotReturn(boolean value);

	@Override
	FunctionDefinitionNode getDefinition();

	/**
	 * Returns the function scope associated to this function. This is the scope
	 * in which the ordinary labels are declared. It is the outermost scope of
	 * the function body.
	 * 
	 * @return the function scope associated to this function
	 */
	Scope getScope();

	/**
	 * Returns the set of functions that call this function either by name or
	 * through a pointer dereference (the latter is relation is safely
	 * overapproximated).
	 * 
	 * Transitive calling relationships are not reflected in this set, i.e., if
	 * a calls b which calls c, then a is not in getCallers() of c (unless of
	 * course a directly calls c as well).
	 * 
	 * The set is initially empty; a call to
	 * {@link edu.udel.cis.vsl.abc.analysis.common.CallAnalyzer#analyze(edu.udel.cis.vsl.abc.ast.IF.AST)}
	 * will populate it.
	 * 
	 * @return the set of functions that call this function
	 */
	Set<Function> getCallers();

	/**
	 * Returns the set of functions called by this function either by name or
	 * through a pointer dereference (the latter is relation is safely
	 * overapproximated).
	 * 
	 * Transitive calling relationships are not reflected in this set, i.e., if
	 * a calls b which calls c, then c is not in getCallees() of a (unless of
	 * course a directly calls c as well).
	 * 
	 * The set is initially empty; a call to
	 * {@link edu.udel.cis.vsl.abc.analysis.common.CallAnalyzer#analyze(edu.udel.cis.vsl.abc.ast.IF.AST)}
	 * will populate it.
	 * 
	 * @return the set of functions called by this function
	 */
	Set<Function> getCallees();

	// TODO clean up contract getter and setter methods
	/**
	 * Add a {@link ContractNode} which represents a contract clause.
	 * 
	 * @param contract
	 *            A node representing a contract clause.
	 */
	void addContract(ContractNode contract);

	/**
	 * Returns a {@link Iterator} for a set of contract clauses.
	 * 
	 * @return
	 */
	Iterator<ContractNode> getContracts();
	// TODO: perhaps more information is needed. About each parameter:
	// does it have static extent? What is the extent (constant
	// or expression)?

	/*
	 * The word "static" may appear between the brackets in certain situations.
	 * See C11 6.7.6.3(7) for its meaning. It can only be used in the
	 * declaration of a function parameter.
	 */

}
