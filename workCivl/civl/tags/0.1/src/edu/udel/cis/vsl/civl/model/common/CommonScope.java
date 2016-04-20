/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common;

import java.io.PrintStream;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.Function;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.type.ArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.ProcessType;
import edu.udel.cis.vsl.civl.model.IF.type.Type;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * A scope.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonScope implements Scope {

	private Scope parent;
	private Variable[] variables;
	private Set<Scope> children = new HashSet<Scope>();
	private Collection<Variable> procRefs = new HashSet<Variable>();
	private int id;
	private Function function;

	/**
	 * A scope.
	 * 
	 * @param parent
	 *            The containing scope of this scope. Only null for the
	 *            outermost scope of the designated "System" function.
	 * 
	 * @param variables
	 *            The set of variables in this scope.
	 */
	public CommonScope(Scope parent, Set<Variable> variables, int id) {
		this.parent = parent;
		this.variables = new Variable[variables.size()];
		for (Variable v : variables) {
			assert this.variables[v.vid()] == null;
			this.variables[v.vid()] = v;
			v.setScope(this);
			checkProcRef(v);
		}
		this.id = id;
	}

	/**
	 * @return The containing scope of this scope.
	 */
	public Scope parent() {
		return parent;
	}

	/**
	 * @return The set of variables contained in this scope.
	 */
	public Set<Variable> variables() {
		return new LinkedHashSet<Variable>(Arrays.asList(variables));
	}

	/**
	 * @return The number of variables contained in this scope.
	 */
	public int numVariables() {
		return variables.length;
	}

	/**
	 * @return Get the variable at position i.
	 */
	public Variable getVariable(int i) {
		return variables[i];
	}

	/**
	 * @return The id of this scope.
	 */
	public int id() {
		return id;
	}

	/**
	 * @return The scopes contained by this scope.
	 */
	public Set<Scope> children() {
		return children;
	}

	/**
	 * @param parent
	 *            The containing scope of this scope.
	 */
	public void setParent(Scope parent) {
		this.parent = parent;
	}

	/**
	 * @param variables
	 *            The set of variables contained in this scope.
	 */
	public void setVariables(Set<Variable> variables) {
		this.variables = new Variable[variables.size()];
		for (Variable v : variables) {
			assert this.variables[v.vid()] == null;
			this.variables[v.vid()] = v;
			checkProcRef(v);
		}
	}

	/**
	 * @param children
	 *            The scopes contained by this scope.
	 */
	public void setChildren(Set<Scope> children) {
		this.children = children;
	}

	/**
	 * @param A
	 *            new scope contained by this scope.
	 */
	public void addChild(Scope child) {
		children.add(child);
	}

	/**
	 * A new variable in this scope.
	 */
	public void addVariable(Variable variable) {
		Variable[] oldVariables = variables;
		variables = new Variable[oldVariables.length + 1];
		for (int i = 0; i < oldVariables.length; i++) {
			variables[i] = oldVariables[i];
		}
		assert variable.vid() == oldVariables.length;
		variables[oldVariables.length] = variable;
		checkProcRef(variable);
		variable.setScope(this);
	}

	/**
	 * Get the variable associated with an identifier. If this scope does not
	 * contain such a variable, parent scopes will be recursively checked.
	 * 
	 * @param name
	 *            The identifier for the variable.
	 * @return The model representation of the variable in this scope hierarchy,
	 *         or null if not found.
	 */
	public Variable variable(Identifier name) {
		for (Variable v : variables) {
			if (v.name().equals(name)) {
				return v;
			}
		}
		if (parent != null) {
			return parent.variable(name);
		}
		return null;
	}

	/**
	 * Get the variable at the specified array index.
	 * 
	 * @param vid
	 *            The index of the variable. Should be in the range
	 *            [0,numVariable()-1].
	 * @return The variable at the index.
	 */
	public Variable variable(int vid) {
		return variables[vid];
	}

	/**
	 * @param function
	 *            The function containing this scope.
	 */
	public void setFunction(Function function) {
		this.function = function;
	}

	/**
	 * @return The function containing this scope.
	 */
	public Function function() {
		return function;
	}

	/**
	 * @return The identifier of the function containing this scope.
	 */
	public Identifier functionName() {
		return function.name();
	}

	/**
	 * A variables has a "procRefType" if it is of type Process or if it is an
	 * array with element of procRefType.
	 * 
	 * @return A collection of the variables in this scope with a procRefType.
	 */
	public Collection<Variable> variablesWithProcrefs() {
		return procRefs;
	}

	/**
	 * Checks if a variables is a procRefType. If it is, it gets added to
	 * procRefs.
	 * 
	 * @param v
	 *            The variable being checked.
	 */
	private void checkProcRef(Variable variable) {
		boolean procRefType = false;
		
		if (variable.type() instanceof ProcessType) {
			procRefType = true;
		} else if (variable.type() instanceof ArrayType) {
			Type baseType = ((ArrayType) variable.type()).baseType();
			
			while (baseType instanceof ArrayType) {
				baseType = ((ArrayType) baseType).baseType();
			}
			if (baseType instanceof ProcessType) {
				procRefType = true;
			}
		}
		if (procRefType) {
			procRefs.add(variable);
		}
	}

	@Override
	public String toString() {
		String result = "Variables : {";

		for (int i = 0; i < variables.length; i++) {
			if (i != 0) {
				result += ", ";
			}
			result += variables[i].toString();
		}
		result += "}";
		return result;
	}

	/**
	 * Print the scope and all children.
	 * 
	 * @param prefix
	 *            String prefix to print on each line
	 * @param out
	 *            The PrintStream to use for printing.
	 */
	public void print(String prefix, PrintStream out) {
		String parentID = "";

		if (parent == null) {
			parentID += "null";
		} else {
			parentID += parent.id();
		}
		out.println(prefix + "scope " + id + " (parent: " + parentID + ")");
		for (Variable v : variables) {
			out.println(prefix + "| " + v);
		}
		for (Scope child : children) {
			if (child.function().equals(function)) {
				child.print(prefix + "| ", out);
			}
		}
		out.flush();
	}

	public int getVid(Variable staticVariable) {
		int result = -1;

		for (int i = 0; i < variables.length; i++) {
			if (variables[i].equals(staticVariable)) {
				result = i;
				break;
			}
		}
		// TODO If not found, either throw error here or catch higher up
		return result;
	}

}
