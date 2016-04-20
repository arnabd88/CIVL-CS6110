/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF;

import java.io.PrintStream;
import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.contract.FunctionContract;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLFunctionType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.util.IF.Pair;

/**
 * A CIVL function.
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
	 * The id of this function in its containing scope
	 * 
	 * @return the id of this function
	 */
	public int fid();

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

	// /**
	// * @param returnType
	// * The return type of this function.
	// */
	// public void setReturnType(CIVLType returnType);

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
	public boolean isRootFunction();

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
	void simplify();

	/**
	 * performs purely local analysis for each statement/location of this
	 * function. No-op for system functions.
	 */
	void purelyLocalAnalysis();

	/**
	 * returns the variables that are used as the operand of the address-of
	 * operator and are visible from the given lexical scope.
	 * 
	 * @param scope
	 *            a lexical scope
	 * @return returns the variables that are used as the operand of the
	 *         address-of operator and are visible from the given lexical scope.
	 */
	Set<Variable> variableAddressedOf(Scope scope);

	/**
	 * returns the variables that are used as the operand of the address-of
	 * operator.
	 * 
	 * @return returns the variables that are used as the operand of the
	 *         address-of operator and are visible from the given lexical scope.
	 */
	Set<Variable> variableAddressedOf();

	/**
	 * returns the type of this function.
	 * 
	 * @return the type of this function.
	 */
	CIVLFunctionType functionType();

	/**
	 * Is this a system function? A system function doesn't contain a function
	 * body and it is implemented by a library component in Java.
	 * 
	 * @return true iff this function is a system function.
	 */
	boolean isSystemFunction();

	/**
	 * Is this an atomic function? An atomic function is declared with the
	 * specifier <code>$atomic_f</code>. Note that abstract functions and system
	 * functions are all atomic although they don't have the
	 * <code>$atomic_f</code> specifier.
	 * 
	 * @return
	 */
	boolean isAtomicFunction();

	/**
	 * Is this an abstract function?
	 * 
	 * @return true iff this function is an abstract function.
	 */
	boolean isAbstractFunction();

	/**
	 * Is this a normal function that contains a function body defined in the
	 * source code?
	 * 
	 * @return true iff this is a normal function that contains a function body
	 *         defined in the source code.
	 */
	boolean isNormalFunction();

	/**
	 * updates the return type of this function
	 * 
	 * @param returnType
	 *            the type to be used as the return type of this function
	 */
	void setReturnType(CIVLType returnType);

	/**
	 * updates the types of the parameters of this function
	 * 
	 * @param types
	 *            the types to be used as the parameter types
	 */
	void setParameterTypes(CIVLType[] types);

	/**
	 * returns the string representation of all un-reached code (if any) in this
	 * function.
	 * 
	 * @return the string representation of all un-reached code (if any) in this
	 *         function
	 */
	StringBuffer unreachedCode();

	/********************** Function contracts methods ***********************/
	/**
	 * Possible valid consequence is a valid contract expression which is
	 * POSSIBLE a consequence of the whole contract Notice that consequences
	 * only come from requirements
	 * 
	 * @param validConsequences
	 */
	void addPossibleValidConsequence(Pair<Expression, Integer> validConsequences);

	/**
	 * Possible valid consequence is a valid contract expression which is
	 * POSSIBLE a consequence of the whole contract Notice that consequences
	 * only come from requirements
	 * 
	 * @param validConsequences
	 */
	List<Pair<Expression, Integer>> getPossibleValidConsequences();

	/**
	 * returns true if and only if the function is contracted.
	 * 
	 * @return
	 */
	boolean isContracted();

	/**
	 * returns the contract specification of this function.
	 * 
	 * @return
	 */
	FunctionContract functionContract();

	/**
	 * sets the contract of this function.
	 * 
	 * @param contract
	 */
	void setFunctionContract(FunctionContract contract);

	void computePathconditionOfLocations(ModelFactory modelFactory);
}
