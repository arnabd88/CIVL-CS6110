/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.variable;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.model.common.CommonSourceable;

/**
 * A variable.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * @author Timothy J. McClory (tmcclory)
 * 
 */
public class CommonVariable extends CommonSourceable implements Variable {

	private CIVLType type;
	private Identifier name;
	private boolean isConst;
	private boolean isInput;
	private int vid;
	private Scope scope;
	private int hashCode;

	/**
	 * A variable.
	 * 
	 * @param type
	 *            The type of the variable.
	 * @param name
	 *            The name of this variable.
	 * @param vid
	 *            The index of this variable in its scope.
	 */
	public CommonVariable(CIVLSource source, CIVLType type, Identifier name,
			int vid) {
		super(source);
		this.type = type;
		this.name = name;
		this.vid = vid;
		computeHashCode();
	}

	/**
	 * @return The index of this variable in its scope.
	 */
	public int vid() {
		return vid;
	}

	/**
	 * @return The type of this variable.
	 */
	public CIVLType type() {
		return type;
	}

	/**
	 * @return Whether this variable is a const.
	 */
	public boolean isConst() {
		return isConst;
	}

	/**
	 * @return Whether this variable is an extern.
	 */
	public boolean isInput() {
		return isInput;
	}

	/**
	 * @param type
	 *            The type of this variable.
	 */
	public void setType(CIVLType type) {
		this.type = type;
		computeHashCode();
	}

	/**
	 * @param isConst
	 *            Whether this variable is a const.
	 */
	public void setConst(boolean isConst) {
		this.isConst = isConst;
		computeHashCode();
	}

	/**
	 * @param value
	 *            Whether this variable is an extern.
	 */
	public void setIsInput(boolean value) {
		this.isInput = value;
	}

	/**
	 * @return The name of this variable.
	 */
	public Identifier name() {
		return name;
	}

	/**
	 * @param scope
	 *            The scope to which this variable belongs.
	 */
	public void setScope(Scope scope) {
		this.scope = scope;
	}

	/**
	 * @return The scope of this variable.
	 */
	public Scope scope() {
		return scope;
	}

	@Override
	public String toString() {
		String result = "";

		if (isConst) {
			result += "const ";
		}
		if (isInput) {
			result += "$input ";
		}
		result += name + " : " + type;
		return result;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		return hashCode;
	}
	
	private void computeHashCode() {
		final int prime = 31;
		int result = 1;
		// result = prime * result + ((extent == null) ? 0 : extent.hashCode());
		result = prime * result + (isConst ? 1231 : 1237);
		result = prime * result + ((name == null) ? 0 : name.hashCode());
		hashCode = prime * result + ((type == null) ? 0 : type.hashCode());
	}
	

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	// @Override
	// public boolean equals(Object obj) {
	// if (this == obj)
	// return true;
	// if (obj == null)
	// return false;
	// if (getClass() != obj.getClass())
	// return false;
	// Variable other = (Variable) obj;
	// if (extent == null) {
	// if (other.extent != null)
	// return false;
	// } else if (!extent.equals(other.extent))
	// return false;
	// if (isConst != other.isConst)
	// return false;
	// if (isSync != other.isSync)
	// return false;
	// if (name == null) {
	// if (other.name != null)
	// return false;
	// } else if (!name.equals(other.name))
	// return false;
	// if (type == null) {
	// if (other.type != null)
	// return false;
	// } else if (!type.equals(other.type))
	// return false;
	// return true;
	// }

}
