package edu.udel.cis.vsl.civl.state.IF;

import java.io.PrintStream;
import java.util.BitSet;

import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * A DynamicScope is a runtime instance of a static scope. It assigns a value to
 * each variable in the static scope. The values are symbolic expressions of the
 * appropriate types.
 * 
 * @author siegel
 * 
 */
public interface DynamicScope {

	/**
	 * Returns the lexical (static) scope of which this dynamic scope is an
	 * instance.
	 * 
	 * A single static scope may have many (or 0) dynamic scope instances
	 * associated to it, but each dynamic scope is an instance of exactly one
	 * static scope.
	 * 
	 * @return the static scope associated to this dynamic scope
	 */
	Scope lexicalScope();

	/**
	 * Gets the value of the variable with variable ID vid. The variables
	 * belonging to a static scope are numbered starting from 0.
	 * 
	 * @param vid
	 *            the variable ID, an integer in the range [0,numVars-1], where
	 *            numVars is the number of variables in the static scope
	 * @return the value associated to the specified variable
	 */
	SymbolicExpression getValue(int vid);

	/**
	 * Sets the value assigned to the vid-th variable. If this dynamic scope is
	 * mutable, this method modifies this dynamic scope and returns this.
	 * Otherwise, it returns a new dynamic scope which is equivalent to this one
	 * except that the value assigned to the variable is the given value.
	 * 
	 * @param vid
	 *            the variable ID
	 * @param value
	 *            the value to assign to that variable
	 * @return an instance of DynamicScope obtained by modifying this instance
	 *         to reflect the new assignment
	 */
	DynamicScope setValue(int vid, SymbolicExpression value);

	/**
	 * Returns an iterable object over the variable values. The iteration is
	 * guaranteed to give the values in variable ID order.
	 * 
	 * @return iterable over variable values, starting from variable with vid 0
	 *         and going up
	 */
	Iterable<SymbolicExpression> getValues();

	/**
	 * Prints a human-readable representation of this dynamic scope. The prefix
	 * is a string that pre-pended to each line of the output. It is typically
	 * something like "|  |  ", used to give a tabbed tree structure to the
	 * output.
	 * 
	 * @param out
	 *            print stream to which output is sent
	 * @param prefix
	 *            a string to prepend to each line of output
	 */
	void print(PrintStream out, String prefix);

	/**
	 * Returns the number of variable values stored in the dynamic scope. The
	 * number of variable values should be the same as the number of variables
	 * of the associated lexical scope.
	 * 
	 * @return the number of variable values stored in the dynamic scope.
	 */
	int numberOfValues();

	// /**
	// * This identifier is not part of the state. It is never renamed, helping
	// to
	// * identify a specific dynamic scope when scopes get collected.
	// *
	// * @return The identifier of this scope.
	// */
	// int identifier();

	// /**
	// * The identifier of the parent of this dyscope in the dyscope tree.
	// Returns
	// * -1 when this is the root scope.
	// *
	// * @return The identifier of the parent of this dyscope in the dyscope
	// tree.
	// */
	// int getParentIdentifier();

	// /**
	// * This name of the dynamic scope, which is not part of the state and is
	// * immutable. It is <code>"d" + identifier</code>.
	// *
	// * @return The name of this dynamic scope.
	// */
	// String name();

	/**
	 * Returns the reachers field.
	 * 
	 * @return the reachers field
	 */
	BitSet getReachers();

	/**
	 * Returns the dyscope ID of the parent of this dynamic scope in the dyscope
	 * tree. If this is the root dyscope (i.e., the lexicalScope is the root
	 * static scope), returns -1.
	 * 
	 * @return The dyscope ID of the parent of this dyscope or -1
	 */
	int getParent();
}
