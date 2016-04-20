/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF;

import java.io.PrintStream;
import java.util.Set;
import java.util.List;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * A function.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface CIVLFunction extends Sourceable {

	/**
	 * @return The name of this function.
	 */
	public Identifier name();

	/**
	 * @return The list of parameters.
	 */
	public List<Variable> parameters();

	/**
	 * @return The return type of this function.
	 */
	public CIVLType returnType();

	/**
	 * @return The set of scopes in this function.
	 */
	public Set<Scope> scopes();

	/**
	 * @return The outermost local scope in this function.
	 */
	public Scope outerScope();

	/**
	 * @return The scope containing this function.
	 */
	public Scope containingScope();

	/**
	 * @return The set of statements in this function.
	 */
	public Set<Statement> statements();

	/**
	 * @return The first location in this function.
	 */
	public Location startLocation();

	/**
	 * @return The set of locations in this function.
	 */
	public Set<Location> locations();

	/**
	 * @return The precondition for this function. Null if not set.
	 */
	public Expression precondition();

	/**
	 * @return The postcondition for this function. Null if not set.
	 */
	public Expression postcondition();

	/**
	 * @return The model to which this function belongs.
	 */
	Model model();

	/**
	 * @param statements
	 *            The set of statements in this function.
	 */
	public void setStatements(Set<Statement> statements);

	/**
	 * @param startLocation
	 *            The first location in this function.
	 */
	public void setStartLocation(Location startLocation);

	/**
	 * @param locations
	 *            The set of locations in this function.
	 */
	public void setLocations(Set<Location> locations);

	/**
	 * @param location
	 *            The new location to add.
	 */
	public void addLocation(Location location);

	/**
	 * @param statement
	 *            The new statement to add.
	 */
	public void addStatement(Statement statement);

	/**
	 * @param name
	 *            The name of this function.
	 */
	public void setName(Identifier name);

	/**
	 * @param parameters
	 *            The list of parameters.
	 */
	public void setParameters(List<Variable> parameters);

	/**
	 * @param returnType
	 *            The return type of this function.
	 */
	public void setReturnType(CIVLType returnType);

	/**
	 * @param scopes
	 *            The set of scopes in this function.
	 */
	public void setScopes(Set<Scope> scopes);

	/**
	 * @param outerScope
	 *            The outermost local scope of this function.
	 */
	public void setOuterScope(Scope outerScope);

	/**
	 * @param containingScope
	 *            The scope containing this function.
	 */
	public void setContainingScope(Scope containingScope);

	/**
	 * @param precondition
	 *            The precondition for this function.
	 */
	public void setPrecondition(Expression precondition);

	/**
	 * @param postcondition
	 *            The postcondition for this function.
	 */
	public void setPostcondition(Expression postcondition);

	/**
	 * @param model
	 *            The Model to which this function belongs.
	 */
	void setModel(Model model);

	/**
	 * Print the function.
	 * 
	 * @param prefix
	 *            String prefix to print on each line
	 * @param out
	 *            The PrintStream to use for printing.
	 * @param isDebug
	 *            True iff the debugging option is enabled, when more
	 *            information will be printed.
	 */
	public void print(String prefix, PrintStream out, boolean isDebug);

	/**
	 * 
	 * @return Is this the outermost function?
	 */
	public boolean isSystem();

	/**
	 * Remove all locations that satisfies the following conditions:
	 * <ol>
	 * <li>has exactly one outgoing statement and</li>
	 * <li>the statement is a no-op with the guard being the true boolean
	 * expression.</li>
	 * </ol>
	 * Meanwhile, have to redirect each statement that targets at the no-op
	 * location to the target of the no-op location. For example, let l(s->l',
	 * ...) be a location l with statement s going to l' ... l1 (s1 -> l2, s2 ->
	 * l3), l2 ([true]no-op -> l4), l3(), l(4) After applying simplify(), should
	 * be l1 (s1 -> l4, s2 -> l3), l3(), l4()
	 */
	public void simplify();

	public void purelyLocalAnalysis();

}
