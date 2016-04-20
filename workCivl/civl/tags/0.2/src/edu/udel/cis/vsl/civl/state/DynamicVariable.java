/**
 * 
 */
package edu.udel.cis.vsl.civl.state;

import edu.udel.cis.vsl.civl.model.IF.variable.Variable;


/**
 * A dynamic variable.
 * 
 * DOES NOT MAKE SENSE.   This has a reference to a dynamic scope state.
 * Shouldn't it just be an ID?
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class DynamicVariable {

	private boolean hashed = false;

	private int hashCode = -1;

	private Variable staticVariable;
	private DynamicScope scope;

	/**
	 * A dynamic variable.
	 * 
	 * @param staticVariable
	 *            The static variable corresponding to this dynamic variable.
	 * @param scope
	 *            The dynamic scope containing this dynamic variable.
	 */
	DynamicVariable(Variable staticVariable, DynamicScope scope) {
		this.staticVariable = staticVariable;
		this.scope = scope;
	}

	/**
	 * @return The static variable corresponding to this dynamic variable.
	 */
	public Variable staticVariable() {
		return staticVariable;
	}

	/**
	 * @return The dynamic scope containing this dynamic variable.
	 */
	public DynamicScope scope() {
		return scope;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		if (hashed) {
			return hashCode;
		} else {
			final int prime = 31;
			int result = 1;
			result = prime * result + ((scope == null) ? 0 : scope.hashCode());
			result = prime
					* result
					+ ((staticVariable == null) ? 0 : staticVariable.hashCode());
			hashCode = result;
			hashed = true;
			return result;
		}
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
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		DynamicVariable other = (DynamicVariable) obj;
		if (scope == null) {
			if (other.scope != null)
				return false;
		} else if (!scope.equals(other.scope))
			return false;
		if (staticVariable == null) {
			if (other.staticVariable != null)
				return false;
		} else if (!staticVariable.equals(other.staticVariable))
			return false;
		return true;
	}

}
