/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import edu.udel.cis.vsl.abc.program.IF.Program;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.MallocStatement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLBundleType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * A model of a CIVL program.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonModel extends CommonSourceable implements Model {

	private LinkedList<CIVLFunction> functions;
	private CIVLFunction system;
	private ModelFactory modelFactory;
	private String name = "";
	private Map<String, Variable> externVariables;
	private CIVLType queueType;
	private CIVLType messageType;
	private CIVLBundleType bundleType;
	private Program program;
	private ArrayList<MallocStatement> mallocStatements;

	private boolean hasFscanf;

	/**
	 * A model of a Chapel program.
	 * 
	 * @param source
	 *            The CIVL source of the model
	 * @param factory
	 *            The ModelFactory responsible for creating this model.
	 * @param system
	 *            The designated outermost function, called "System."
	 */
	public CommonModel(CIVLSource source, ModelFactory factory,
			CIVLFunction system, Program program) {
		super(source);
		this.modelFactory = factory;
		this.system = system;
		functions = new LinkedList<>();
		functions.add(system);
		this.program = program;
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
	public Set<CIVLFunction> functions() {
		return new HashSet<CIVLFunction>(functions);
	}

	/**
	 * @return The designated outermost function "System."
	 */
	public CIVLFunction system() {
		return system;
	}

	/**
	 * @param functions
	 *            The set of all functions in the model.
	 */
	public void setFunctions(Set<CIVLFunction> functions) {
		this.functions = new LinkedList<CIVLFunction>(functions);
	}

	/**
	 * @param system
	 *            The designated outermost function "System."
	 */
	public void setSystem(CIVLFunction system) {
		this.system = system;
	}

	/**
	 * @param function
	 *            The function to be added to the model.
	 */
	public void addFunction(CIVLFunction function) {
		functions.add(function);
	}

	/**
	 * @param queueType
	 *            The queue type used by this model.
	 */
	public void setQueueType(CIVLType queueType) {
		this.queueType = queueType;
	}

	/**
	 * @param messageType
	 *            The message type used by this model.
	 */
	public void setMessageType(CIVLType messageType) {
		this.messageType = messageType;
	}

	/**
	 * Get a function based on its name.
	 * 
	 * @param name
	 *            The name of the function.
	 * @return The function with the given name. Null if not found.
	 */
	public CIVLFunction function(String name) {
		for (CIVLFunction f : functions) {
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
	@Override
	public void print(PrintStream out, boolean isDebug) {
		out.print("Model");
		if (name != null)
			out.print(" " + name);
		out.println();
		for (CIVLFunction function : functions) {
			function.print(" | ", out, isDebug);
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

	/**
	 * Update the list of malloc statements
	 * 
	 * @param mallocStatements
	 *            the list of malloc statements
	 */
	public void setMallocStatements(ArrayList<MallocStatement> mallocStatements) {
		this.mallocStatements = mallocStatements;
	}

	@Override
	public int getNumMallocs() {
		return mallocStatements.size();
	}

	@Override
	public MallocStatement getMalloc(int index) {
		return mallocStatements.get(index);
	}

	@Override
	public CIVLType queueType() {
		return queueType;
	}

	@Override
	public CIVLType mesageType() {
		return messageType;
	}

	@Override
	public CIVLBundleType bundleType() {
		return this.bundleType;
	}

	@Override
	public void setBundleType(CIVLBundleType type) {
		this.bundleType = type;
	}

	@Override
	public void complete() {
		this.system.outerScope().complete();
		this.renumberLocations();
	}

	private void renumberLocations() {
		int id = 0;

		for (CIVLFunction function : this.functions) {
			function.simplify();
			for (Location location : function.locations()) {
				location.setId(id++);
			}
		}
	}

	@Override
	public void setHasFscanf(boolean value) {
		this.hasFscanf = value;
	}

	@Override
	public boolean hasFscanf() {
		return this.hasFscanf;
	}

	@Override
	public Program program() {
		return this.program;
	}

	@Override
	public void printUnreachedCode(PrintStream out) {
		boolean noUnreachedCode = true;

		for (CIVLFunction function : functions) {
			StringBuffer unreached = function.unreachedCode();

			if (!unreached.toString().equals("")) {
				noUnreachedCode = false;
				out.print(unreached);
			}
		}
		if (noUnreachedCode)
			out.println("This program doesn't have any unreachable code.");
		out.println();
	}
}
