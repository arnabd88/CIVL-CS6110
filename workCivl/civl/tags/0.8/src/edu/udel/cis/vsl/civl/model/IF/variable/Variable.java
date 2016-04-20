/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.variable;

import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.Sourceable;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;

/**
 * A static variable. Each variable is declared in some static scope. Each
 * variable has a name, a type, and an integer variable ID. The ID is in the
 * range [0,n-1], where n is the number of variables in the static scope
 * containing this variable. This variable's ID is unique within its scope.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * @author Timothy J. McClory (tmcclory)
 * 
 */
public interface Variable extends Sourceable {

	/**
	 * 
	 * @return The index of this variable in the containing scope.
	 */
	int vid();

	/**
	 * @return The type of this variable.
	 */
	CIVLType type();

	/**
	 * @return Whether this variable is a const.
	 */
	boolean isConst();

	/**
	 * @return Whether this variable is an input.
	 */
	boolean isInput();
	
	/**
	 * @return Whether this variable is a bound variable.
	 */
	boolean isBound();
	
	/**
	 * @param type
	 *            The type of this variable.
	 */
	void setType(CIVLType type);

	/**
	 * @param isConst
	 *            Whether this variable is a const.
	 */
	void setConst(boolean isConst);

	/**
	 * @param value
	 *            Whether this variable is an input.
	 */
	void setIsInput(boolean value);

	/**
	 * @param value
	 *            Whether this variable is a bound variable.
	 */
	void setIsBound(boolean value);

	/**
	 * @return The name of this variable.
	 */
	Identifier name();

	/**
	 * @param scope
	 *            The scope to which this variable belongs.
	 */
	void setScope(Scope scope);

	/**
	 * @return The scope of this variable.
	 */
	Scope scope();

	/**
	 * return true iff the variable is purely local, i.e., v is purely local if
	 * there is no &v in the model, and in v's scope, if there are no spawned
	 * functions that refer to v
	 * 
	 * @return
	 */
	boolean purelyLocal();

	void setPurelyLocal(boolean pl);

}
