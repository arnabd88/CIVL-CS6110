package edu.udel.cis.vsl.civl.state.trans;

import java.io.PrintStream;
import java.util.Arrays;

import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.state.IF.DynamicScope;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * Implementation of {@link DynamicScope} using the Transient Pattern.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * @author Timothy J. McClory (tmcclory)
 * @author Stephen F. Siegel (siegel)
 * 
 */
public class TransientDynamicScope extends TransientObject implements
		DynamicScope {

	/*********************** Static Fields **************************/

	/**
	 * Print debugging info?
	 */
	private static boolean debug = false;

	/**
	 * How many instances of this class have been created?
	 */
	static long instanceCount = 0;

	/********************** Instance Fields *************************/

	/**
	 * Non-null static scope to which this dynamic scope is associated.
	 */
	private Scope lexicalScope;

	/**
	 * Non-null array of variable values. The symbolic expression in position i
	 * is the value of the variable of index i. Each entry is non-null, but may
	 * be the "null symbolic expression" ("NULL").
	 */
	private SymbolicExpression[] variableValues;

	/************************ Constructors ***************************/

	/**
	 * Creates a new dynamic scope in which all variable values are assigned the
	 * same value.
	 * 
	 * @param lexicalScope
	 *            The lexical scope corresponding to this dynamic scope
	 * @param value
	 *            the value to associated to every variable in the scope
	 */
	TransientDynamicScope(Scope lexicalScope, SymbolicExpression value) {
		super(instanceCount++);
		assert lexicalScope != null;
		this.lexicalScope = lexicalScope;
		{
			int numVars = lexicalScope.numVariables();

			variableValues = new SymbolicExpression[numVars];
			for (int i = 0; i < numVars; i++)
				variableValues[i] = value;
		}
	}

	/**
	 * Creates a new dynamic scope with the given lexical scope and variable
	 * values. The variable values are not copied, so don't try to re-use them
	 * or modify them.
	 * 
	 * @param lexicalScope
	 *            the static scope of which this dynamic scope is an instance
	 * @param variableValues
	 *            the array of variable values (in order by vid, from 0, up)
	 */
	TransientDynamicScope(Scope lexicalScope,
			SymbolicExpression[] variableValues) {
		super(instanceCount++);
		assert variableValues != null
				&& variableValues.length == lexicalScope.numVariables();
		this.lexicalScope = lexicalScope;
		this.variableValues = variableValues;
	}

	/********************** Private Methods *************************/

	/****************** Package Private Methods **********************/

	int numberOfVariables() {
		return variableValues.length;
	}

	DynamicScope setValues(SymbolicExpression[] values) {
		if (mutable) {
			this.variableValues = values;
			return this;
		}
		return new TransientDynamicScope(lexicalScope, values);
	}

	/********************* Methods from Object ***********************/

	@Override
	public String toString() {
		return "DynamicScope " + identifier() + " [staticId="
				+ lexicalScope.id() + "]";
	}

	/***************** Methods from TransientObject ******************/

	@Override
	protected int computeHashCode() {
		return lexicalScope.hashCode() ^ Arrays.hashCode(variableValues);
	}

	@Override
	protected boolean computeEquals(Object object) {
		if (object instanceof TransientDynamicScope) {
			TransientDynamicScope that = (TransientDynamicScope) object;

			return lexicalScope.equals(that.lexicalScope)
					&& Arrays.equals(variableValues, that.variableValues);
		}
		return false;
	}

	/****************** Methods from DynamicScope ********************/

	@Override
	public SymbolicExpression getValue(int vid) {
		return variableValues[vid];
	}

	@Override
	public Scope lexicalScope() {
		return lexicalScope;
	}

	@Override
	public void print(PrintStream out, String prefix) {
		int numVars = lexicalScope.numVariables();

		out.println(prefix + "Dyscope " + identifier() + " (static="
				+ lexicalScope.id() + ")");
		for (int i = 0; i < numVars; i++) {
			Variable variable = lexicalScope.variable(i);
			SymbolicExpression value = variableValues[i];

			out.print(prefix + "| " + variable.name() + " = ");
			if (debug)
				out.println(value.toStringBufferLong());
			else
				out.println(value + " : " + value.type());
		}
		out.flush();
	}

	@Override
	public DynamicScope setValue(int vid, SymbolicExpression value) {
		if (mutable) {
			variableValues[vid] = value;
			return this;
		} else {
			int n = numberOfVariables();
			SymbolicExpression[] newVariableValues = new SymbolicExpression[n];

			System.arraycopy(variableValues, 0, newVariableValues, 0, n);
			newVariableValues[vid] = value;
			return new TransientDynamicScope(lexicalScope, newVariableValues);
		}
	}

	@Override
	public Iterable<SymbolicExpression> getValues() {
		return Arrays.asList(variableValues);
	}

}
