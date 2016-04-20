/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common;

import java.io.PrintStream;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.Vector;

import edu.udel.cis.vsl.civl.model.IF.Function;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.type.Type;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * A function.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonFunction implements Function{

	private Identifier name;
	private Vector<Variable> parameters;
	private Type returnType;
	private Set<Scope> scopes;
	private Scope outerScope;
	private Scope containingScope;
	private Set<Statement> statements;
	private Location startLocation;
	private Set<Location> locations;
	private Expression precondition = null;
	private Expression postcondition = null;

	/**
	 * A function.
	 * 
	 * @param name
	 *            The name of this function.
	 * @param parameters
	 *            The list of parameters.
	 * @param returnType
	 *            The return type of this function.
	 * @param containingScope
	 *            The scope containing this function.
	 * @param startLocation
	 *            The first location in the function.
	 */
	public CommonFunction(Identifier name, Vector<Variable> parameters,
			Type returnType, Scope containingScope, Location startLocation,
			ModelFactory factory) {
		this.name = name;
		this.parameters = parameters;
		this.returnType = returnType;
		this.containingScope = containingScope;
		scopes = new HashSet<Scope>();
		outerScope = factory.scope(containingScope,
				new LinkedHashSet<Variable>(), this);
		for (Variable variable : parameters) {
			outerScope.addVariable(variable);
		}
		scopes.add(outerScope);
		locations = new LinkedHashSet<Location>();
		this.startLocation = startLocation;
		if (startLocation != null) {
			locations.add(this.startLocation);
		}
		statements = new LinkedHashSet<Statement>();
	}

	/**
	 * @return The name of this function.
	 */
	public Identifier name() {
		return name;
	}

	/**
	 * @return The list of parameters.
	 */
	public Vector<Variable> parameters() {
		return parameters;
	}

	/**
	 * @return The return type of this function.
	 */
	public Type returnType() {
		return returnType;
	}

	/**
	 * @return The set of scopes in this function.
	 */
	public Set<Scope> scopes() {
		return scopes;
	}

	/**
	 * @return The outermost local scope in this function.
	 */
	public Scope outerScope() {
		return outerScope;
	}

	/**
	 * @return The scope containing this function.
	 */
	public Scope containingScope() {
		return containingScope;
	}

	/**
	 * @return The set of statements in this function.
	 */
	public Set<Statement> statements() {
		return statements;
	}

	/**
	 * @return The first location in this function.
	 */
	public Location startLocation() {
		return startLocation;
	}

	/**
	 * @return The set of locations in this function.
	 */
	public Set<Location> locations() {
		return locations;
	}

	/**
	 * @return The precondition for this function. Null if not set.
	 */
	public Expression precondition() {
		return precondition;
	}

	/**
	 * @return The postcondition for this function. Null if not set.
	 */
	public Expression postcondition() {
		return postcondition;
	}

	/**
	 * @param statements
	 *            The set of statements in this function.
	 */
	public void setStatements(Set<Statement> statements) {
		this.statements = statements;
	}

	/**
	 * @param startLocation
	 *            The first location in this function.
	 */
	public void setStartLocation(Location startLocation) {
		this.startLocation = startLocation;
		if (!locations.contains(startLocation)) {
			locations.add(startLocation);
		}
	}

	/**
	 * @param locations
	 *            The set of locations in this function.
	 */
	public void setLocations(Set<Location> locations) {
		this.locations = locations;
	}

	/**
	 * @param location
	 *            The new location to add.
	 */
	public void addLocation(Location location) {
		locations.add(location);
	}

	/**
	 * @param statement
	 *            The new statement to add.
	 */
	public void addStatement(Statement statement) {
		statements.add(statement);
	}

	/**
	 * @param name
	 *            The name of this function.
	 */
	public void setName(Identifier name) {
		this.name = name;
	}

	/**
	 * @param parameters
	 *            The list of parameters.
	 */
	public void setParameters(Vector<Variable> parameters) {
		this.parameters = parameters;
	}

	/**
	 * @param returnType
	 *            The return type of this function.
	 */
	public void setReturnType(Type returnType) {
		this.returnType = returnType;
	}

	/**
	 * @param scopes
	 *            The set of scopes in this function.
	 */
	public void setScopes(Set<Scope> scopes) {
		this.scopes = scopes;
	}

	/**
	 * @param outerScope
	 *            The outermost local scope of this function.
	 */
	public void setOuterScope(Scope outerScope) {
		this.outerScope = outerScope;
	}

	/**
	 * @param containingScope
	 *            The scope containing this function.
	 */
	public void setContainingScope(Scope containingScope) {
		this.containingScope = containingScope;
	}

	/**
	 * @param precondition
	 *            The precondition for this function.
	 */
	public void setPrecondition(Expression precondition) {
		this.precondition = precondition;
	}

	/**
	 * @param postcondition
	 *            The postcondition for this function.
	 */
	public void setPostcondition(Expression postcondition) {
		this.postcondition = postcondition;
	}

	/**
	 * Print the function.
	 * 
	 * @param prefix
	 *            String prefix to print on each line
	 * @param out
	 *            The PrintStream to use for printing.
	 */
	public void print(String prefix, PrintStream out) {
		Iterator<Variable> iter;

		out.println(prefix + "function " + name);
		if (precondition != null) {
			out.println(prefix + "| requires " + precondition);
		}
		if (postcondition != null) {
			out.println(prefix + "| ensures " + postcondition);
		}
		out.println(prefix + "| formal parameters");
		iter = parameters.iterator();
		while (iter.hasNext()) {
			out.println(prefix + "| | " + iter.next().name());
		}
		outerScope.print(prefix + "| ", out);
		out.println(prefix + "| locations (start=" + startLocation.id() + ")");
		for (Location loc : locations) {
			loc.print(prefix + "| | ", out);
			out.flush();
		}
	}

	@Override
	public String toString() {
		String result = name.name() + "(";

		for (int i = 0; i < parameters.size(); i++) {
			if (i != 0) {
				result += ",";
			}
			result += parameters.get(i);
		}
		result += ")";
		return result;
	}

}
