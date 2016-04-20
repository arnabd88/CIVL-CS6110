/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common;

import java.io.PrintStream;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLBundleType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPointerType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLStructOrUnionType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.type.StructOrUnionField;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * A scope.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonScope extends CommonSourceable implements Scope {

	/**
	 * The parent scope of this scope. Each scope has exactly one parent scope,
	 * except for the root scope which has no parent.
	 */
	private Scope parent;
	private Variable[] variables;
	private Map<String, CIVLFunction> functions;
	private Set<Scope> children = new LinkedHashSet<Scope>();
	private Collection<Variable> procRefs = new HashSet<Variable>();
	private Collection<Variable> scopeRefs = new HashSet<Variable>();
	private Collection<Variable> pointers = new HashSet<Variable>();
	private int id;
	private CIVLFunction function;

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
	public CommonScope(CIVLSource source, Scope parent,
			Set<Variable> variables, int id) {
		super(source);
		this.parent = parent;
		this.variables = new Variable[variables.size()];
		this.functions = new HashMap<>();
		for (Variable v : variables) {
			assert this.variables[v.vid()] == null;
			this.variables[v.vid()] = v;
			v.setScope(this);
			// checkProcRef(v);
			// checkPointer(v);
			// checkScopeRef(v);
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
			// checkProcRef(v);
			// checkPointer(v);
			// checkScopeRef(v);
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

	@Override
	public void addFunction(CIVLFunction function) {
		this.functions.put(function.name().name(), function);
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
		// checkProcRef(variable);
		// checkScopeRef(variable);
		// checkPointer(variable);
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

	@Override
	public boolean containsVariable(String name) {
		for (Variable v : variables) {
			if (v.name().name().equals(name)) {
				return true;
			}
		}
		return false;
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
	public void setFunction(CIVLFunction function) {
		this.function = function;
	}

	/**
	 * @return The function containing this scope.
	 */
	public CIVLFunction function() {
		return function;
	}

	/**
	 * @return The identifier of the function containing this scope.
	 */
	public Identifier functionName() {
		return function.name();
	}

	/**
	 * A variables has a "procRefType" if it is of type Process, if it is an
	 * array with element of procRefType, or if it is a struct with fields of
	 * procRefType.
	 * 
	 * @return A collection of the variables in this scope with a procRefType.
	 */
	public Collection<Variable> variablesWithProcrefs() {
		return procRefs;
	}

	/**
	 * A variables has a "scopeRefType" if it is of type Scope, if it is an
	 * array with element of scopeRefType, if it is a struct with fields of
	 * scopeRefType, or if it contains a pointer.
	 * 
	 * @return A collection of the variables in this scope with a scopeRefType.
	 */
	public Collection<Variable> variablesWithScoperefs() {
		return scopeRefs;
	}

	/**
	 * A variable contains a pointer type if it is of type PointerType, if it is
	 * an array with elements containing pointer type, or if it is a struct with
	 * fields containing pointer type.
	 * 
	 * @return A collection of the variables in this scope containing pointer
	 *         types.
	 */
	public Collection<Variable> variablesWithPointers() {
		return pointers;
	}

	/**
	 * Checks if a variables is a procRefType. If it is, it gets added to
	 * procRefs.
	 * 
	 * @param v
	 *            The variable being checked.
	 */
	private void checkProcRef(Variable variable) {
		boolean procRefType = containsProcType(variable.type());

		if (procRefType) {
			procRefs.add(variable);
		}
	}

	/**
	 * Checks if a variables is a scopeRefType. If it is, it gets added to
	 * scopeRefs.
	 * 
	 * @param v
	 *            The variable being checked.
	 */
	private void checkScopeRef(Variable variable) {
		CIVLType type = variable.type();
		boolean scopeRefType = containsScopeType(type);

		if (scopeRefType) {
			scopeRefs.add(variable);
		} else if (containsPointerType(type)) {
			scopeRefs.add(variable);
		}
	}

	/**
	 * Checks if a variables is a pointer. If it is, it gets added to pointers.
	 * 
	 * @param v
	 *            The variable being checked.
	 */
	private void checkPointer(Variable variable) {
		boolean pointerType = containsPointerType(variable.type());

		if (pointerType) {
			pointers.add(variable);
		}
	}

	private boolean containsPointerType(CIVLType type) {
		boolean containsPointerType = false;

		if (type instanceof CIVLPointerType) {
			containsPointerType = true;
		} else if (type instanceof CIVLArrayType) {
			containsPointerType = containsPointerType(((CIVLArrayType) type)
					.elementType());
		} else if (type instanceof CIVLStructOrUnionType) {
			for (StructOrUnionField f : ((CIVLStructOrUnionType) type).fields()) {
				boolean fieldContainsPointer = containsPointerType(f.type());

				containsPointerType = containsPointerType
						|| fieldContainsPointer;
			}
		} else if (type.isHeapType()) {
			// Heaps start out incomplete, so let's assume this is true for now.
			// Ultimately we'd like to only have this be true if the heap
			// contains pointer types.
			containsPointerType = true;
		} else if (type.isBundleType()) {
			List<CIVLType> types = ((CIVLBundleType) type).types();

			for (CIVLType elementType : types) {
				boolean elementContainsPointer = containsPointerType(elementType);

				containsPointerType = containsPointerType
						|| elementContainsPointer;
			}
		}
		return containsPointerType;
	}

	private boolean containsScopeType(CIVLType type) {
		boolean containsScopeType = false;

		if (type.isScopeType()) {
			containsScopeType = true;
		} else if (type.isArrayType()) {
			containsScopeType = containsScopeType(((CIVLArrayType) type)
					.elementType());
		} else if (type.isStructType()) {
			for (StructOrUnionField f : ((CIVLStructOrUnionType) type).fields()) {
				boolean fieldContainsScope = containsScopeType(f.type());

				containsScopeType = containsScopeType || fieldContainsScope;
			}
		} else if (type.isHeapType()) {
			// Heaps start out incomplete, so let's assume this is true for now.
			// Ultimately we'd like to only have this be true if the heap
			// contains scope types.
			containsScopeType = true;
		} else if (type.isBundleType()) {
			List<CIVLType> types = ((CIVLBundleType) type).types();

			for (CIVLType elementType : types) {
				boolean elementContainsScope = containsScopeType(elementType);

				containsScopeType = containsScopeType || elementContainsScope;
			}
		}
		return containsScopeType;
	}

	private boolean containsProcType(CIVLType type) {
		boolean containsProcType = false;

		if (type.isProcessType()) {
			containsProcType = true;
		} else if (type.isArrayType()) {
			containsProcType = containsProcType(((CIVLArrayType) type)
					.elementType());
		} else if (type.isStructType()) {
			for (StructOrUnionField f : ((CIVLStructOrUnionType) type).fields()) {
				boolean fieldContainsProc = containsProcType(f.type());

				containsProcType = containsProcType || fieldContainsProc;
			}
		} else if (type.isHeapType()) {
			// Heaps start out incomplete, so let's assume this is true for now.
			// Ultimately we'd like to only have this be true if the heap
			// contains process types.
			containsProcType = true;
		} else if (type.isBundleType()) {
			List<CIVLType> types = ((CIVLBundleType) type).types();

			for (CIVLType elementType : types) {
				boolean elementContainsProc = containsProcType(elementType);

				containsProcType = containsProcType || elementContainsProc;
			}
		}
		return containsProcType;
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

	@Override
	public void print(String prefix, PrintStream out, boolean isDebug) {
		String parentID = "";

		if (parent == null) {
			parentID += "null";
		} else {
			parentID += parent.id();
		}
		out.println(prefix + "scope " + id + " (parent: " + parentID + ")");
		for (Variable v : variables) {
			if (isDebug) {
				out.println(prefix + "| " + v + " (purely local)");
			} else {
				out.println(prefix + "| " + v);
			}
		}
		for (Scope child : children) {
			if (child.function().equals(function)) {
				child.print(prefix + "| ", out, isDebug);
			}
		}
		out.flush();
	}

	@Override
	public CIVLFunction getFunction(Identifier name) {
		String functionName = name.name();

		if (this.functions.containsKey(functionName))
			return functions.get(functionName);
		if (this.parent != null)
			return this.parent.getFunction(name);
		return null;
	}

	@Override
	public CIVLFunction getFunction(String name) {
		if (this.functions.containsKey(name))
			return functions.get(name);
		if (this.parent != null)
			return this.parent.getFunction(name);
		return null;
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

	@Override
	public Model model() {
		return function.model();
	}

	@Override
	public boolean isDescendantOf(Scope anc) {
		Scope parent = this.parent;

		while (parent != null) {
			if (parent.id() == anc.id())
				return true;
			parent = parent.parent();
		}

		return false;
	}

	@Override
	public Variable variable(String name) {
		for (Variable v : variables) {
			if (v.name().name().equals(name)) {
				return v;
			}
		}
		return null;
	}

	@Override
	public void complete() {
		for (Variable v : variables) {
			this.checkPointer(v);
			this.checkScopeRef(v);
			this.checkProcRef(v);
		}
		if (children != null)
			for (Scope child : children)
				child.complete();
	}

}
