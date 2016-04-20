package edu.udel.cis.vsl.civl.state.immutable;

import java.io.PrintStream;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Collection;
import java.util.Map;

import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.state.IF.DynamicScope;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * An ImmutableDynamicScope represents the state of a single dynamic scope in
 * the state of a CIVL model. It is an instance of a static (lexical) scope. It
 * assigns to each variable in the static scope a value, which is a symbolic
 * expression of the appropriate type.
 * 
 * As the name suggests an ImmutableDynamicScope is immutable, at least in all
 * ways visible to the user.
 * 
 * Instances of this class may be "flyweighted" (see the Flyweight Pattern). The
 * methods {@link #makeCanonic(SymbolicUniverse)} and {@link #isCanonic()}
 * support this pattern.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * @author Timothy J. McClory (tmcclory)
 * @author Stephen F. Siegel (siegel)
 * 
 */
public class ImmutableDynamicScope implements DynamicScope {

	/* *************************** Static Fields *************************** */

	/**
	 * If true, print debugging information.
	 */
	private final static boolean debug = false;

	/* ************************** Instance Fields ************************** */

	/**
	 * Is this instance the canonic representative of its equivalence class
	 * under the "equals" method?
	 */
	boolean canonic = false;

	/**
	 * If the hash code has been computed, it is cached here.
	 */
	private int hashCode = -1;

	/**
	 * Has the hash code been computed?
	 */
	private boolean hashed = false;

	/**
	 * Non-null static scope to which this dynamic scope is associated.
	 */
	private Scope lexicalScope;

	/**
	 * The dyscope ID of the parent of this dynamic scope in the dynamic scope
	 * tree, or -1 if this is the root (and therefore has no parent).
	 */
	private int parent;

	/**
	 * Sets of PIDs of processes that can "reach" this dynamic scope.
	 */
	private BitSet reachers;

	/**
	 * Values associated to the variables declared in the lexicalScope. This is
	 * a non-null array of symbolic expressions. The symbolic expression in
	 * position i is the value associated to variable i; it is non-null, but may
	 * be the symbolic expression NULL.
	 */
	private SymbolicExpression[] variableValues;

	/* **************************** Constructors *************************** */

	/**
	 * Constructs a new immutable dynamic scope with the given fields. No data
	 * is cloned---the given parameters become the fields of the new instance.
	 * 
	 * @param lexicalScope
	 *            the static scope of which this dynamic scope is an instance
	 * @param parent
	 *            the dyscope ID of the parent of this dynamic scope in the
	 *            dyscope tree
	 * @param variableValues
	 *            the array of values associated to the variables declared in
	 *            the static scope
	 * @param reachers
	 *            the set of PIDs of processes that can reach this dyscope
	 */
	ImmutableDynamicScope(Scope lexicalScope, int parent,
			SymbolicExpression[] variableValues, BitSet reachers) {
		assert variableValues != null
				&& variableValues.length == lexicalScope.numVariables();
		this.lexicalScope = lexicalScope;
		this.parent = parent;
		this.variableValues = variableValues;
		this.reachers = reachers;
	}

	/* ********************** Package-private Methods ********************** */

	/**
	 * Returns the dyscope ID of the parent of this dynamic scope in the dyscope
	 * tree. If this is the root dyscope (i.e., the lexicalScope is the root
	 * static scope), returns -1.
	 * 
	 * @return The dyscope ID of the parent of this dyscope or -1
	 */
	int getParent() {
		return parent;
	}

	/**
	 * Returns a new immutable dynamic scope which is equivalent to this one,
	 * except that the parent field is replaced by the given value.
	 * 
	 * @param parent
	 *            new value for the parent field
	 * @return new instance same as original but with new parent value
	 */
	ImmutableDynamicScope setParent(int parent) {
		return parent == this.parent ? this : new ImmutableDynamicScope(
				lexicalScope, parent, variableValues, reachers);
	}

	/**
	 * Returns the reachers field.
	 * 
	 * @return the reachers field
	 */
	BitSet getReachers() {
		return reachers;
	}

	/**
	 * Returns a new immutable dynamic scope which is equivalent to this one,
	 * except that the reachers field is replaced by the given value.
	 * 
	 * @param reachers
	 *            new value for the reachers field
	 * @return new instance same as original but with new reachers value
	 */
	ImmutableDynamicScope setReachers(BitSet reachers) {
		return new ImmutableDynamicScope(lexicalScope, parent, variableValues,
				reachers);
	}

	/**
	 * How many processes can reach this dynamic scope? A process p can reach a
	 * dynamic scope d iff there is a path starting from a dynamic scope which
	 * is referenced in a frame on p's call stack to d, following the "parent"
	 * edges in the scope tree.
	 * 
	 * @return the number of processes which can reach this dynamic scope
	 */
	int numberOfReachers() {
		return reachers.cardinality();
	}

	/**
	 * Is this dynamic scope reachable by the process with the given PID?
	 * 
	 * @param pid
	 * @return true iff this dynamic scope is reachable from the process with
	 *         pid PID
	 */
	boolean reachableByProcess(int pid) {
		return reachers.get(pid);
	}

	/**
	 * Returns a new immutable dynamic scope which is equivalent to this one,
	 * except that the variableValues field is replaced by the given value.
	 * 
	 * @param newVariableValues
	 *            new value for the variableValues field
	 * @return new instance same as original but with new variableValues value
	 */
	ImmutableDynamicScope setVariableValues(
			SymbolicExpression[] newVariableValues) {
		return new ImmutableDynamicScope(lexicalScope, parent,
				newVariableValues, reachers);
	}

	/**
	 * Returns the number of variables in this dynamic scope; this is the same
	 * as the number in the associated static scope; this is just provided for
	 * convenience.
	 * 
	 * @return number of variables in this scope
	 */
	int numberOfVariables() {
		return variableValues.length;
	}

	/**
	 * Returns a copy of the variable values.
	 * 
	 * @return a copy of the variable values
	 */
	SymbolicExpression[] copyValues() {
		SymbolicExpression[] newValues = new SymbolicExpression[variableValues.length];

		System.arraycopy(variableValues, 0, newValues, 0, variableValues.length);
		return newValues;
	}

	/**
	 * Makes this instance the canonic representative of its equivalence class
	 * under "equals". Makes all the variable values canonic as well.
	 * 
	 * @param universe
	 *            the symbolic universe that is used to make the variable values
	 *            canonic
	 */
	void makeCanonic(SymbolicUniverse universe) {
		int numVars = variableValues.length;

		canonic = true;
		for (int i = 0; i < numVars; i++)
			variableValues[i] = universe.canonic(variableValues[i]);
	}

	/**
	 * Is this instance the unique representative of its equivalence class?
	 * 
	 * @return true iff this is the canonic representative of its equivalence
	 *         class
	 */
	boolean isCanonic() {
		return canonic;
	}

	/**
	 * Prints detailed representation of this dynamic scope.
	 * 
	 * @param out
	 *            print stream to which output should be sent
	 * @param id
	 *            a name to use for this dynamic scope in the print out (e.g.,
	 *            an ID number)
	 * @param prefix
	 *            a string to preprend to each line of output
	 */
	void print(PrintStream out, String id, String prefix) {
		int numVars = lexicalScope.numVariables();
		int bitSetLength = reachers.length();
		boolean first = true;

		out.println(prefix + "dyscope " + id + " (parent=" + parent
				+ ", static=" + lexicalScope.id() + ")");
		out.print(prefix + "| reachers = {");
		for (int j = 0; j < bitSetLength; j++) {
			if (reachers.get(j)) {
				if (first)
					first = false;
				else
					out.print(",");
				out.print(j);
			}
		}
		out.println("}");
		out.println(prefix + "| variables");
		for (int i = 0; i < numVars; i++) {
			Variable variable = lexicalScope.variable(i);
			SymbolicExpression value = variableValues[i];

			out.print(prefix + "| | " + variable.name() + " = ");
			if (debug)
				out.println(value.toStringBufferLong());
			else
				out.println(value);
		}
		out.flush();
	}

	ImmutableDynamicScope updateDyscopeIds(
			Map<SymbolicExpression, SymbolicExpression> scopeSubMap,
			SymbolicUniverse universe, int newParentId) {
		Collection<Variable> scopeVariableIter = lexicalScope
				.variablesWithScoperefs();
		SymbolicExpression[] newValues = null;

		for (Variable variable : scopeVariableIter) {
			int vid = variable.vid();
			SymbolicExpression oldValue = variableValues[vid];

			if (oldValue != null && !oldValue.isNull()) {
				SymbolicExpression newValue = universe.substitute(oldValue,
						scopeSubMap);

				if (oldValue != newValue) {
					if (newValues == null)
						newValues = copyValues();
					newValues[vid] = newValue;
				}
			}
		}
		return newValues == null ? setParent(newParentId)
				: new ImmutableDynamicScope(lexicalScope, newParentId,
						newValues, reachers);
	}

	/*************************** Methods from Object *************************/

	/**
	 * Determines if the given object is equal to this one. Returns true iff:
	 * (1) obj is an instance of ImmutableDynamicScope, (2) the lexical scopes
	 * are equal, (3) the parent fields are equal, (4) the variableValues arrays
	 * have the same length and corresponding values are equal, and (5) the
	 * reachers sets are equal.
	 * 
	 * This implementation is optimized by taking advantage of immutability and
	 * flyweighting.
	 */
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj instanceof ImmutableDynamicScope) {
			ImmutableDynamicScope that = (ImmutableDynamicScope) obj;

			if (canonic && that.canonic)
				return false;
			if (hashed && that.hashed && hashCode != that.hashCode)
				return false;
			return lexicalScope == that.lexicalScope && parent == that.parent
					&& Arrays.equals(variableValues, that.variableValues)
					&& reachers.equals(that.reachers);
		}
		return false;
	}

	@Override
	public int hashCode() {
		if (!hashed) {
			hashCode = lexicalScope.hashCode() ^ (1017 * parent)
					^ Arrays.hashCode(variableValues) ^ reachers.hashCode();
			hashed = true;
		}
		return hashCode;
	}

	@Override
	public String toString() {
		return "DynamicScope[static=" + lexicalScope.id() + ", parent="
				+ parent + "]";
	}

	/* ********************** Methods from DynamicScope ******************** */

	@Override
	public SymbolicExpression getValue(int vid) {
		return variableValues[vid];
	}

	@Override
	public Iterable<SymbolicExpression> getValues() {
		return Arrays.asList(variableValues);
	}

	@Override
	public Scope lexicalScope() {
		return lexicalScope;
	}

	@Override
	public void print(PrintStream out, String prefix) {
		print(out, "", prefix);
	}

	@Override
	public DynamicScope setValue(int vid, SymbolicExpression value) {
		int n = numberOfVariables();
		SymbolicExpression[] newVariableValues = new SymbolicExpression[n];

		System.arraycopy(variableValues, 0, newVariableValues, 0, n);
		newVariableValues[vid] = value;
		return new ImmutableDynamicScope(lexicalScope, parent,
				newVariableValues, reachers);
	}

	@Override
	public int numberOfValues() {
		return this.variableValues.length;
	}

	/* ************************ Other Public Methods *********************** */
	// none
}
