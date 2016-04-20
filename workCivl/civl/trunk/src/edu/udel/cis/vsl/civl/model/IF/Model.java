/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF;

import java.io.PrintStream;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.udel.cis.vsl.abc.program.IF.Program;
import edu.udel.cis.vsl.civl.model.IF.statement.MallocStatement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLBundleType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * A model of a program.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface Model extends Sourceable {

	/**
	 * @return The model factory that created this model.
	 */
	public ModelFactory factory();

	/**
	 * @param name
	 *            The name of this model.
	 */
	public void setName(String name);

	/**
	 * @return The name of this model.
	 */
	public String name();

	/**
	 * @return The set of all functions in the model.
	 */
	public Set<CIVLFunction> functions();

	/**
	 * @return The designated outermost function "System."
	 */
	public CIVLFunction system();

	/**
	 * @param functions
	 *            The set of all functions in the model.
	 */
	public void setFunctions(Set<CIVLFunction> functions);

	/**
	 * @param system
	 *            The designated outermost function "System."
	 */
	public void setSystem(CIVLFunction system);

	/**
	 * @param function
	 *            The function to be added to the model.
	 */
	public void addFunction(CIVLFunction function);

	/**
	 * Get a function based on its name.
	 * 
	 * @param name
	 *            The name of the function.
	 * @return The function with the given name. Null if not found.
	 */
	public CIVLFunction function(String name);

	/**
	 * Print the model.
	 * 
	 * @param out
	 *            The PrintStream used to print the model.
	 * @param isDebug
	 *            True iff the debugigng option is enabled, when more
	 *            information will be printed, such as purely local marks,
	 *            location loops, etc.
	 */
	public void print(PrintStream out, boolean isDebug);

	/**
	 * @param externVariables
	 *            Map of names to variables for all extern variables used in
	 *            this model.
	 */
	public void setExternVariables(Map<String, Variable> externVariables);

	/**
	 * @return Map of names to variables for all extern variables used in this
	 *         model.
	 */
	public Map<String, Variable> externVariables();

	/**
	 * @return the number of malloc and malloc-equivalent (e.g., gcomm_create)
	 *         statements in the model
	 */
	int getNumMallocs();

	/**
	 * @param index
	 *            the index of the malloc statement
	 * @return the malloc statement of the given index
	 */
	MallocStatement getMalloc(int index);

	/**
	 * 
	 * @param queueType
	 *            The queue type used by this model.
	 */
	void setQueueType(CIVLType queueType);

	/**
	 * @param messageType
	 *            The message type used by this model.
	 */
	void setMessageType(CIVLType messageType);

	/**
	 * @return The queue type used by this model.
	 */
	CIVLType queueType();

	/**
	 * @return The message type used by this model.
	 */
	CIVLType mesageType();

	/**
	 * 
	 * @return The bundle type used by this model.
	 */
	CIVLBundleType bundleType();

	/**
	 * updates the bundle type of the model
	 * 
	 * @param type
	 *            the bundle type
	 */
	void setBundleType(CIVLBundleType type);

	/**
	 * Complete the model. This should be called as the last call for
	 * manipulating the model.
	 */
	void complete();

	/**
	 * updates the flag which denotes either the model contains any fscanf call
	 * or not.
	 * 
	 * @param value
	 */
	void setHasFscanf(boolean value);

	/**
	 * 
	 * @return true iff the model contains any fscanf call
	 */
	boolean hasFscanf();

	/**
	 * @return the program object associates with this model
	 */
	Program program();

	/**
	 * prints the unreached code of the model
	 * 
	 * @param out
	 *            the output stream
	 */
	void printUnreachedCode(PrintStream out);

	/**
	 * Return the output variables of this model, which all belong to the root
	 * scope.
	 * 
	 * @return the output variables of this model, which all belong to the root
	 *         scope
	 */
	List<Variable> outputVariables();
}
