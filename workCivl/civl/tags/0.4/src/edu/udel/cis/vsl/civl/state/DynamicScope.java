package edu.udel.cis.vsl.civl.state;

import java.io.PrintStream;
import java.util.Arrays;
import java.util.BitSet;

import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * Represents state of a dynamic scope.
 * 
 * Participates in Flyweight Pattern.
 * 
 * TODO: Note that two scopes are different if they have different parentIDs.
 * Think about this. Would it be better to have a separate component of the
 * state which specifies the parent structure, say an array parents of length
 * numScopes: DynamicScope[] parents?
 * 
 * Other components have references to the scope id: StackEntry.
 * 
 * TODO: could use BitSet to record the set of processes that can reach this
 * dynamic scope. Would need to re-do bit set when processes change. Is a sparse
 * representation better?
 * 
 * operations: add a process, remove a process, renumber procs by shifting
 * 
 * @author Timothy K. Zirkel (zirkel)
 * @author Timothy J. McClory (tmcclory)
 * 
 */
public class DynamicScope {

	private static boolean debug = false;

	private boolean hashed = false;

	private int hashCode = -1;

	boolean canonic = false;

	/**
	 * Non-null static scope to which this dynamic scope is associated.
	 */
	private Scope lexicalScope;

	/**
	 * TODO: CONSIDER this: move this field out of DynamicScope and into a
	 * separate state component recording parent structure to facilitate re-use.
	 */
	private int parent;

	/**
	 * Non-null array of variable values. The symbolic expression in position i
	 * is the value of the variable of index i. May contain null values.
	 */
	private SymbolicExpression[] variableValues;

	/**
	 * Sets of PIDs of processes that can reach this dynamic scope.
	 */
	private BitSet reachers;

	/**
	 * A dynamic scope in which all variable values are null.
	 * 
	 * @param lexicalScope
	 *            The lexical scope corresponding to this dynamic scope.
	 * @param parent
	 *            The parent of this dynamic scope. -1 only for the topmost
	 *            dynamic scope.
	 */
	DynamicScope(Scope lexicalScope, int parent, BitSet reachers) {
		assert lexicalScope != null;
		this.lexicalScope = lexicalScope;
		this.parent = parent;
		this.reachers = reachers;
		variableValues = new SymbolicExpression[lexicalScope.numVariables()]; // FIX
	}

	DynamicScope(Scope lexicalScope, int parent,
			SymbolicExpression[] variableValues, BitSet reachers) {
		assert variableValues != null
				&& variableValues.length == lexicalScope.numVariables();
		this.lexicalScope = lexicalScope;
		this.parent = parent;
		this.variableValues = variableValues;
		this.reachers = reachers;
	}

	DynamicScope changeParent(int newParent) {
		return new DynamicScope(lexicalScope, newParent, variableValues,
				reachers);
	}

	DynamicScope changeReachers(BitSet newBitSet) {
		return new DynamicScope(lexicalScope, parent, variableValues, newBitSet);
	}

	DynamicScope changeVariableValues(SymbolicExpression[] newVariableValues) {
		return new DynamicScope(lexicalScope, parent, newVariableValues,
				reachers);
	}

	public SymbolicExpression getValue(int vid) {
		return variableValues[vid];
	}

	public int numberOfVariables() {
		return variableValues.length;
	}

	/**
	 * How many processes can reach this dynamic scope? A process p can reach a
	 * dynamic scope d iff there is a path starting from a dynamic scope which
	 * is referenced in a frame on p's call stack to d, following the "parent"
	 * edges in the scope tree.
	 * 
	 * @return the number of processes which can reach this dynamic scope
	 */
	public int numberOfReachers() {
		return reachers.cardinality();
	}

	/**
	 * Is this dynamic scope reachable by the process with the given PID?
	 * 
	 * @param pid
	 * @return true iff this dynamic scope is reachable from the process with
	 *         pid PID
	 */
	public boolean reachableByProcess(int pid) {
		return reachers.get(pid);
	}

	/**
	 * @return The lexical scope corresponding to this dynamic scope.
	 */
	public Scope lexicalScope() {
		return lexicalScope;
	}

	// TODO: move this to factory....
	/**
	 * @return The parent of this dynamic scope. Null only for the topmost
	 *         dynamic scope.
	 */
	int parent() {
		return parent;
	}

	/**
	 * Change to publice, since we need to get the owners of a scope in POR (Enabler.java)
	 * @return
	 */
	public BitSet reachers() {
		return reachers;
	}

	/**
	 * @return Copy the set of values in this scopes.
	 */
	SymbolicExpression[] copyValues() {
		SymbolicExpression[] newValues = new SymbolicExpression[variableValues.length];

		System.arraycopy(variableValues, 0, newValues, 0, variableValues.length);
		return newValues;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		if (!hashed) {
			final int prime = 31;

			hashCode = 1;
			hashCode = prime * hashCode + lexicalScope.hashCode();
			hashCode = prime * hashCode + parent;
			hashCode = prime * hashCode + Arrays.hashCode(variableValues);
			hashCode = prime * hashCode + reachers.hashCode();
			hashed = true;
		}
		return hashCode;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj instanceof DynamicScope) {
			DynamicScope that = (DynamicScope) obj;

			if (canonic && that.canonic)
				return false;
			if (hashed && that.hashed && hashCode != that.hashCode)
				return false;
			if (!lexicalScope.equals(that.lexicalScope))
				return false;
			if (parent != that.parent)
				return false;
			if (!Arrays.equals(variableValues, that.variableValues))
				return false;
			if (!reachers.equals(that.reachers))
				return false;
			return true;
		}
		return false;
	}

	public void print(PrintStream out, int id, String prefix) {
		int numVars = lexicalScope.numVariables();
		int bitSetLength = reachers.length();
		boolean first = true;

		out.println(prefix + "scope " + id + " (parent=" + parent + ", static="
				+ lexicalScope.id() + ")");
		out.print(prefix + "| reachers: ");
		for (int j = 0; j < bitSetLength; j++) {
			if (reachers.get(j)) {
				if (first)
					first = false;
				else
					out.print(",");
				out.print(j);
			}
		}
		out.println();
		for (int i = 0; i < numVars; i++) {
			Variable variable = lexicalScope.getVariable(i);
			SymbolicExpression value = variableValues[i];

			out.print(prefix + "| " + variable.name() + " = ");
			if (debug)
				out.println(value.toStringBufferLong());
			else
				out.println(value + " : " + value.type());
		}
		out.flush();
	}

	@Override
	public String toString() {
		return "DynamicScope[static=" + lexicalScope.id() + ", parent="
				+ parent + "]";
	}
}
