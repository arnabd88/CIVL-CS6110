/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.model.common.expression.CommonBooleanLiteralExpression;
import edu.udel.cis.vsl.civl.model.common.location.CommonLocation.AtomicKind;
import edu.udel.cis.vsl.civl.model.common.statement.CommonNoopStatement;

/**
 * A function.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonFunction extends CommonSourceable implements CIVLFunction {

	/************************* Instance Fields *************************/

	private Scope containingScope;

	protected boolean isSystem = false;

	private Set<Location> locations;

	private Model model;

	private Identifier name;

	private Scope outerScope;

	private List<Variable> parameters;

	private Expression postcondition = null;

	private Expression precondition = null;

	private CIVLType returnType;

	private Set<Scope> scopes;

	private Location startLocation;

	private Set<Statement> statements;

	/************************** Constructors *************************/

	/**
	 * A function.
	 * 
	 * @param source
	 *            The CIVL source of the function
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
	 * @param factory
	 *            The model factory
	 */
	public CommonFunction(CIVLSource source, Identifier name,
			List<Variable> parameters, CIVLType returnType,
			Scope containingScope, Location startLocation, ModelFactory factory) {
		super(source);
		this.name = name;
		this.parameters = parameters;
		this.returnType = returnType;
		this.containingScope = containingScope;
		scopes = new HashSet<Scope>();
		outerScope = factory.scope(source, containingScope,
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

	/************************** Methods from CIVLFunction *************************/

	/**
	 * @param location
	 *            The new location to add.
	 */
	@Override
	public void addLocation(Location location) {
		locations.add(location);
	}

	/**
	 * @param statement
	 *            The new statement to add.
	 */
	@Override
	public void addStatement(Statement statement) {
		statements.add(statement);
	}

	/**
	 * @return The scope containing this function.
	 */
	@Override
	public Scope containingScope() {
		return containingScope;
	}

	@Override
	public boolean isSystem() {
		return isSystem;
	}

	/**
	 * @return The set of locations in this function.
	 */
	@Override
	public Set<Location> locations() {
		return locations;
	}

	/**
	 * @return The model to which this function belongs.
	 */
	@Override
	public Model model() {
		return model;
	}

	/**
	 * @return The name of this function.
	 */
	@Override
	public Identifier name() {
		return name;
	}

	/**
	 * @return The outermost local scope in this function.
	 */
	@Override
	public Scope outerScope() {
		return outerScope;
	}

	/**
	 * @return The list of parameters.
	 */
	@Override
	public List<Variable> parameters() {
		return parameters;
	}

	/**
	 * @return The postcondition for this function. Null if not set.
	 */
	@Override
	public Expression postcondition() {
		return postcondition;
	}

	/**
	 * @return The precondition for this function. Null if not set.
	 */
	@Override
	public Expression precondition() {
		return precondition;
	}

	@Override
	public void print(String prefix, PrintStream out, boolean isDebug) {
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
		outerScope.print(prefix + "| ", out, isDebug);
		if (!isSystem()) {
			out.println(prefix + "| locations (start=" + startLocation.id()
					+ ")");
			for (Location loc : locations) {
				loc.print(prefix + "| | ", out, isDebug);
			}
		}
		out.flush();
	}

	@Override
	public void purelyLocalAnalysis() {
		Scope funcScope = this.outerScope;

		for (Location loc : this.locations) {
			Iterable<Statement> stmts = loc.outgoing();

			for (Statement s : stmts) {
				s.purelyLocalAnalysisOfVariables(funcScope);
				// TODO functions that are never spawned are to be executed in
				// the same process as the caller
			}
		}
	}

	/**
	 * @return The return type of this function.
	 */
	@Override
	public CIVLType returnType() {
		return returnType;
	}

	/**
	 * @return The set of scopes in this function.
	 */
	@Override
	public Set<Scope> scopes() {
		return scopes;
	}

	/**
	 * @param containingScope
	 *            The scope containing this function.
	 */
	@Override
	public void setContainingScope(Scope containingScope) {
		this.containingScope = containingScope;
	}

	/**
	 * @param locations
	 *            The set of locations in this function.
	 */
	@Override
	public void setLocations(Set<Location> locations) {
		this.locations = locations;
	}

	/**
	 * @param model
	 *            The Model to which this function belongs.
	 */
	@Override
	public void setModel(Model model) {
		this.model = model;
	}

	/**
	 * @param name
	 *            The name of this function.
	 */
	@Override
	public void setName(Identifier name) {
		this.name = name;
	}

	/**
	 * @param outerScope
	 *            The outermost local scope of this function.
	 */
	@Override
	public void setOuterScope(Scope outerScope) {
		this.outerScope = outerScope;
	}

	/**
	 * @param postcondition
	 *            The postcondition for this function.
	 */
	public void setPostcondition(Expression postcondition) {
		this.postcondition = postcondition;
	}

	/**
	 * @param precondition
	 *            The precondition for this function.
	 */
	public void setPrecondition(Expression precondition) {
		this.precondition = precondition;
	}

	/**
	 * @param parameters
	 *            The list of parameters.
	 */
	@Override
	public void setParameters(List<Variable> parameters) {
		this.parameters = parameters;
	}

	/**
	 * @param returnType
	 *            The return type of this function.
	 */
	@Override
	public void setReturnType(CIVLType returnType) {
		this.returnType = returnType;
	}

	/**
	 * @param scopes
	 *            The set of scopes in this function.
	 */
	@Override
	public void setScopes(Set<Scope> scopes) {
		this.scopes = scopes;
	}

	/**
	 * @param startLocation
	 *            The first location in this function.
	 */
	@Override
	public void setStartLocation(Location startLocation) {
		this.startLocation = startLocation;
		if (!locations.contains(startLocation)) {
			locations.add(startLocation);
		}
	}

	/**
	 * @param statements
	 *            The set of statements in this function.
	 */
	@Override
	public void setStatements(Set<Statement> statements) {
		this.statements = statements;
	}

	@Override
	public void simplify() {
		ArrayList<Location> oldLocations = new ArrayList<Location>(
				this.locations);
		int count = oldLocations.size();
		Set<Location> newLocations;
		// The index of locations that can be removed
		ArrayList<Integer> toRemove = new ArrayList<Integer>();

		for (int i = 0; i < count; i++) {
			Location loc = oldLocations.get(i);

			if (loc.atomicKind() != AtomicKind.NONE)
				continue;
			// loc has exactly one statement
			if (loc.getNumOutgoing() == 1) {
				Statement s = loc.getOutgoing(0);

				// The only statement of loc is a no-op statement
				if (s instanceof CommonNoopStatement) {
					Expression guard = s.guard();

					// The guard of the no-op is true
					if (guard instanceof CommonBooleanLiteralExpression) {
						if (((CommonBooleanLiteralExpression) guard).value()) {
							Location target = s.target();

							// Record the index of loc so that it can be
							// removed later
							toRemove.add(i);
							for (int j = 0; j < count; j++) {
								Location curLoc;

								// Do nothing to the locations that are to be
								// removed
								if (toRemove.contains(j))
									continue;
								curLoc = oldLocations.get(j);
								// For each statement of curLoc \in
								// (this.locations - toRemove)
								for (Statement curS : curLoc.outgoing()) {
									Location curTarget = curS.target();

									// Redirect the target location so that
									// no-op location is skipped
									if (curTarget != null
											&& curTarget.id() == loc.id()) {
										// the incoming field is implicitly
										// modified by setTarget()
										curS.setTarget(target);
									}
								}
							}
						}
					}
				}
			}
		}
		newLocations = new LinkedHashSet<Location>();
		for (int k = 0; k < count; k++) {
			if (toRemove.contains(k))
				continue;
			newLocations.add(oldLocations.get(k));
		}
		this.locations = newLocations;
	}

	/**
	 * @return The first location in this function.
	 */
	@Override
	public Location startLocation() {
		return startLocation;
	}

	/**
	 * @return The set of statements in this function.
	 */
	@Override
	public Set<Statement> statements() {
		return statements;
	}

	/************************** Methods from Object *************************/

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
