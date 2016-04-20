/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF;

import java.io.PrintStream;
import java.util.Map;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * A model of a program.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface Model {
	
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
	public Set<Function> functions();

	/**
	 * @return The designated outermost function "System."
	 */
	public Function system();

	/**
	 * @param functions
	 *            The set of all functions in the model.
	 */
	public void setFunctions(Set<Function> functions);

	/**
	 * @param system
	 *            The designated outermost function "System."
	 */
	public void setSystem(Function system);

	/**
	 * @param function
	 *            The function to be added to the model.
	 */
	public void addFunction(Function function);

	/**
	 * Get a function based on its name.
	 * 
	 * @param name
	 *            The name of the function.
	 * @return The function with the given name. Null if not found.
	 */
	public Function function(String name);

	/**
	 * Print the model.
	 * 
	 * @param out
	 *            The PrintStream used to print the model.
	 */
	public void print(PrintStream out);

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

}
