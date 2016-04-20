/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.variable;

import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.type.Type;

/**
 * A variable.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * @author Timothy J. McClory (tmcclory)
 * 
 */
public interface Variable {

	public int vid();

	/**
	 * @return The type of this variable.
	 */
	public Type type();

	/**
	 * @return Whether this variable is a sync variable.
	 */
	public boolean isSync();

	/**
	 * @return Whether this variable is a const.
	 */
	public boolean isConst();

	/**
	 * @return For an array variable, the extent of the array. Null if
	 *         unspecified or not an array.
	 */
	public Expression extent();

	/**
	 * @return Whether this variable is an extern.
	 */
	public boolean isExtern();
	
	/**
	 * @return Whether this variable is an extern.
	 */
	public boolean isConfig();
	
	/**
	 * @param type
	 *            The type of this variable.
	 */
	public void setType(Type type);

	/**
	 * @param isSync
	 *            Whether this variable is a sync variable.
	 */
	public void setSync(boolean isSync);

	/**
	 * @param isConst
	 *            Whether this variable is a const.
	 */
	public void setConst(boolean isConst);

	/**
	 * @param extent
	 *            For an array variable, the extent of the array. Null if
	 *            unspecified or not an array.
	 */
	public void setExtent(Expression extent);

	/**
	 * @param isExtern
	 *            Whether this variable is an extern.
	 */
	public void setIsExtern(boolean isExtern);

	/**
	 * @param isConfig
	 *            Whether this variable is an config.
	 */
	public void setIsConfig(boolean isConfig);

	
	/**
	 * @param vid
	 *            The new vid.
	 */
	public void setVid(int vid);

	/**
	 * @return The name of this variable.
	 */
	public Identifier name();

	// TODO remove setters
	/**
	 * @param name
	 *            The name of this variable.
	 */
	public void setName(Identifier name);

	/**
	 * @param scope
	 *            The scope to which this variable belongs.
	 */
	public void setScope(Scope scope);

	/**
	 * @return The scope of this variable.
	 */
	public Scope scope();

}
