/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common;

import java.io.PrintStream;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.Function;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * A model of a Chapel program.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonModel implements Model {

	private LinkedList<Function> functions;
	private Function system;
	private ModelFactory modelFactory;
	private String name = "";
	private Map<String, Variable> externVariables;

	/**
	 * A model of a Chapel program.
	 * 
	 * @param factory
	 *            The ModelFactory responsible for creating this model.
	 * @param system
	 *            The designated outermost function, called "System."
	 */
	public CommonModel(ModelFactory factory, Function system) {
		this.modelFactory = factory;
		this.system = system;
		functions = new LinkedList<Function>();
		functions.add(system);
	}

	/**
	 * A model of a Chapel program.
	 * 
	 * @param factory
	 *            The ModelFactory responsible for creating this model.
	 * @param system
	 *            The designated outermost function, called "System."
	 * @param functions
	 *            The set of all functions in the model, including "System."
	 */
	public CommonModel(ModelFactory factory, Function system, Set<Function> functions) {
		this.modelFactory = factory;
		this.system = system;
		this.functions = new LinkedList<Function>(functions);
	}

	/**
	 * @return The model factory that created this model.
	 */
	public ModelFactory factory() {
		return modelFactory;
	}

	/**
	 * @param name
	 *            The name of this model.
	 */
	public void setName(String name) {
		this.name = name;
	}

	/**
	 * @return The name of this model.
	 */
	public String name() {
		return name;
	}

	/**
	 * @return The set of all functions in the model.
	 */
	public Set<Function> functions() {
		return new HashSet<Function>(functions);
	}

	/**
	 * @return The designated outermost function "System."
	 */
	public Function system() {
		return system;
	}

	/**
	 * @param functions
	 *            The set of all functions in the model.
	 */
	public void setFunctions(Set<Function> functions) {
		this.functions = new LinkedList<Function>(functions);
	}

	/**
	 * @param system
	 *            The designated outermost function "System."
	 */
	public void setSystem(Function system) {
		this.system = system;
	}

	/**
	 * @param function
	 *            The function to be added to the model.
	 */
	public void addFunction(Function function) {
		functions.add(function);
	}

	/**
	 * Get a function based on its name.
	 * 
	 * @param name
	 *            The name of the function.
	 * @return The function with the given name. Null if not found.
	 */
	public Function function(String name) {
		for (Function f : functions) {
			if (f.name().name().equals(name)) {
				return f;
			}
		}
		return null;
	}

	/**
	 * Print the model.
	 * 
	 * @param out
	 *            The PrintStream used to print the model.
	 */
	public void print(PrintStream out) {
		out.println("Model");
		for (Function function : functions) {
			function.print(" | ", out);
		}
		out.flush();
	}

	/**
	 * @param externVariables
	 *            Map of names to variables for all extern variables used in
	 *            this model.
	 */
	public void setExternVariables(Map<String, Variable> externVariables) {
		this.externVariables = externVariables;
	}

	/**
	 * @return Map of names to variables for all extern variables used in this
	 *         model.
	 */
	public Map<String, Variable> externVariables() {
		return externVariables;
	}

}
