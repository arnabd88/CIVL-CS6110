/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF;

import java.io.PrintStream;
import java.util.Collection;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * A scope.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface Scope extends Sourceable {

	/**
	 * @return The containing scope of this scope.
	 */
	Scope parent();

	/**
	 * @return The set of variables contained in this scope.
	 */
	Set<Variable> variables();

	/**
	 * @return The number of variables contained in this scope.
	 */
	int numVariables();

	/**
	 * @return Get the variable at position i.
	 */
	Variable getVariable(int i);

	/**
	 * @return The id of this scope.
	 */
	int id();

	/**
	 * @return The scopes contained by this scope.
	 */
	Set<Scope> children();

	/**
	 * @return The model to which this scope belongs.
	 */
	Model model();

	/**
	 * @param parent
	 *            The containing scope of this scope.
	 */
	void setParent(Scope parent);

	/**
	 * @param variables
	 *            The set of variables contained in this scope.
	 */
	void setVariables(Set<Variable> variables);

	/**
	 * @param children
	 *            The scopes contained by this scope.
	 */
	void setChildren(Set<Scope> children);

	/**
	 * @param A
	 *            new scope contained by this scope.
	 */
	void addChild(Scope child);

	/**
	 * A new variable in this scope.
	 */
	void addVariable(Variable variable);

	/**
	 * Get the variable associated with an identifier. If this scope does not
	 * contain such a variable, parent scopes will be recursively checked.
	 * 
	 * @param name
	 *            The identifier for the variable.
	 * @return The model representation of the variable in this scope hierarchy,
	 *         or null if not found.
	 */
	Variable variable(Identifier name);

	/**
	 * Get the variable at the specified array index.
	 * 
	 * @param vid
	 *            The index of the variable. Should be in the range
	 *            [0,numVariable()-1].
	 * @return The variable at the index.
	 */
	Variable variable(int vid);

	/**
	 * @param function
	 *            The function containing this scope.
	 */
	void setFunction(CIVLFunction function);

	/**
	 * @return The function containing this scope.
	 */
	CIVLFunction function();

	/**
	 * @return The identifier of the function containing this scope.
	 */
	Identifier functionName();

	/**
	 * A variables has a "procRefType" if it is of type Process or if it is an
	 * array with element of procRefType.
	 * 
	 * @return A collection of the variables in this scope with a procRefType.
	 */
	Collection<Variable> variablesWithProcrefs();

	/**
	 * A variable contains a pointer type if it is of type PointerType, if it is
	 * an array with elements containing pointer type, or if it is a struct with
	 * fields containing pointer type.
	 * 
	 * @return A collection of the variables in this scope containing pointer
	 *         types.
	 */
	Collection<Variable> variablesWithPointers();

	/**
	 * Print the scope and all children.
	 * 
	 * @param prefix
	 *            String prefix to print on each line
	 * @param out
	 *            The PrintStream to use for printing.
	 */
	void print(String prefix, PrintStream out);

	int getVid(Variable staticVariable);

}