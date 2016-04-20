/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.common.CommonSourceable;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * A partial implementation of interface {@link Expression}. This is the root of
 * the expression implementation hierarchy. All expression classes are
 * sub-classes of this class.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public abstract class CommonExpression extends CommonSourceable implements
		Expression {

	// TODO: add field private SymbolicExpression constantValue
	// with setters and getters. Initially null, this is
	// used by expressions which have a constant value.
	// it is an optimization.

	/**
	 * The highest scope accessed by this expression. NULL if no variable is
	 * accessed.
	 */
	private Scope expressionScope = null;

	/**
	 * The lowest scope accessed by this expression. NULL if no variable is
	 * accessed.
	 */
	private Scope lowestScope = null;

	/**
	 * The type of this expression.
	 * 
	 */
	protected CIVLType expressionType = null;

	/**
	 * Does this expression contains any dereference operation?
	 */
	protected boolean hasDerefs;

	/**
	 * Is this expression purely local? An expression is purely local if ...
	 */
	protected boolean purelyLocal = false;

	/**
	 * The constant value of this expression. null by default.
	 */
	protected SymbolicExpression constantValue = null;

	/**
	 * The parent of all expressions.
	 */
	public CommonExpression(CIVLSource source, Scope hscope, Scope lscope,
			CIVLType type) {
		super(source);
		this.lowestScope = lscope;
		this.expressionScope = hscope;
		this.expressionType = type;
	}

	protected abstract boolean expressionEquals(Expression expression);

	@Override
	public boolean hasDerefs() {
		return hasDerefs;
	}

	@Override
	public Scope expressionScope() {
		return expressionScope;
	}

	@Override
	public CIVLType getExpressionType() {
		return expressionType;
	}

	@Override
	public void calculateDerefs() {
		this.hasDerefs = false;
	}

	@Override
	public void purelyLocalAnalysisOfVariables(Scope funcScope) {
	}

	@Override
	public boolean isPurelyLocal() {
		return this.purelyLocal;
	}

	@Override
	public void purelyLocalAnalysis() {
		this.purelyLocal = !this.hasDerefs;
	}

	@Override
	public void replaceWith(ConditionalExpression oldExpression,
			VariableExpression newExpression) {

	}

	@Override
	public Expression replaceWith(ConditionalExpression oldExpression,
			Expression newExpression) {
		return null;
	}

	@Override
	public SymbolicExpression constantValue() {
		return this.constantValue;
	}

	@Override
	public boolean hasConstantValue() {
		return this.constantValue != null;
	}

	@Override
	public void calculateConstantValue(SymbolicUniverse universe) {
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof Expression) {
			Expression that = (Expression) obj;

			if (this.expressionKind() == that.expressionKind())
				return this.expressionEquals(that);
		}
		return false;
	}

	@Override
	public Scope lowestScope() {
		return this.lowestScope;
	}

	@Override
	public boolean containsHere() {
		return false;
	}
}
