/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.variable;

import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.type.Type;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * A variable.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * @author Timothy J. McClory (tmcclory)
 * 
 */
public class CommonVariable implements Variable {

	private Type type;
	private Identifier name;
	private boolean isSync;
	private boolean isConst;
	private boolean isExtern;
	private boolean isConfig;
	private Expression extent = null;
	private int vid;
	private Scope scope;

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
	public CommonVariable(Type type, Identifier name, int vid) {
		this.type = type;
		this.name = name;
		this.vid = vid;
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
	public Type type() {
		return type;
	}

	/**
	 * @return Whether this variable is a sync variable.
	 */
	public boolean isSync() {
		return isSync;
	}

	/**
	 * @return Whether this variable is a const.
	 */
	public boolean isConst() {
		return isConst;
	}

	/**
	 * @return For an array variable, the extent of the array. Null if
	 *         unspecified or not an array.
	 */
	public Expression extent() {
		return extent;
	}

	/**
	 * @return Whether this variable is an extern.
	 */
	public boolean isExtern() {
		return isExtern;
	}
	
	/**
	 * @return Whether this variable is an extern.
	 */
	public boolean isConfig() {
		return isConfig;
	}
	
	/**
	 * @param type
	 *            The type of this variable.
	 */
	public void setType(Type type) {
		this.type = type;
	}

	/**
	 * @param isSync
	 *            Whether this variable is a sync variable.
	 */
	public void setSync(boolean isSync) {
		this.isSync = isSync;
	}

	/**
	 * @param isConst
	 *            Whether this variable is a const.
	 */
	public void setConst(boolean isConst) {
		this.isConst = isConst;
	}

	/**
	 * @param extent
	 *            For an array variable, the extent of the array. Null if
	 *            unspecified or not an array.
	 */
	public void setExtent(Expression extent) {
		this.extent = extent;
	}

	/**
	 * @param isExtern
	 *            Whether this variable is an extern.
	 */
	public void setIsExtern(boolean isExtern) {
		this.isExtern = isExtern;
	}

	/**
	 * @param isConfig
	 *            Whether this variable is an config.
	 */
	public void setIsConfig(boolean isConfig) {
		this.isConfig = isConfig;
	}

	
	/**
	 * @param vid
	 *            The new vid.
	 */
	public void setVid(int vid) {
		this.vid = vid;
	}

	/**
	 * @return The name of this variable.
	 */
	public Identifier name() {
		return name;
	}

	// TODO remove setters
	/**
	 * @param name
	 *            The name of this variable.
	 */
	public void setName(Identifier name) {
		this.name = name;
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
		if (isExtern) {
			result += "$input ";
		}
		result += name + " : " + (isSync ? "sync " : "") + type;
		return result;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((extent == null) ? 0 : extent.hashCode());
		result = prime * result + (isConst ? 1231 : 1237);
		result = prime * result + (isSync ? 1231 : 1237);
		result = prime * result + ((name == null) ? 0 : name.hashCode());
		result = prime * result + ((type == null) ? 0 : type.hashCode());
		return result;
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
