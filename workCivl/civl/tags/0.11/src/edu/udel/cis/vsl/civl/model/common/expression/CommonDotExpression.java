/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.HashSet;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DotExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * @author zirkel
 * 
 */
public class CommonDotExpression extends CommonExpression implements
		DotExpression {

	private Expression structOrUnion;// TODO shall this be of type
										// LHSExpression?
	private int fieldIndex;

	/**
	 * A dot expression is a reference to a field in a struct.
	 * 
	 * @param struct
	 *            The struct referenced by this dot expression.
	 * @param field
	 *            The field referenced by this dot expression.
	 */
	public CommonDotExpression(CIVLSource source, Expression struct,
			int fieldIndex) {
		super(source);
		this.structOrUnion = struct;
		this.fieldIndex = fieldIndex;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see edu.udel.cis.vsl.civl.model.IF.expression.DotExpression#struct()
	 */
	@Override
	public Expression structOrUnion() {
		return structOrUnion;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see edu.udel.cis.vsl.civl.model.IF.expression.DotExpression#field()
	 */
	@Override
	public int fieldIndex() {
		return fieldIndex;
	}

	@Override
	public String toString() {
		return structOrUnion.toString() + "." + fieldIndex;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.DOT;
	}

	@Override
	public void calculateDerefs() {
		this.structOrUnion.calculateDerefs();
		this.hasDerefs = this.structOrUnion.hasDerefs();
	}

	@Override
	public void setPurelyLocal(boolean pl) {
		// TODO what if &(a.index) where a is defined as a struct
		// and index is a field of the struct
	}

	@Override
	public void purelyLocalAnalysisOfVariables(Scope funcScope) {
		this.structOrUnion.purelyLocalAnalysisOfVariables(funcScope);
	}

	@Override
	public void purelyLocalAnalysis() {
		if (this.hasDerefs) {
			this.purelyLocal = false;
			return;
		}

		this.structOrUnion.purelyLocalAnalysis();
		this.purelyLocal = this.structOrUnion.isPurelyLocal();
	}

	@Override
	public void replaceWith(ConditionalExpression oldExpression,
			VariableExpression newExpression) {
		if (structOrUnion == oldExpression) {
			structOrUnion = newExpression;
			return;
		}
		structOrUnion.replaceWith(oldExpression, newExpression);
	}

	@Override
	public Expression replaceWith(ConditionalExpression oldExpression,
			Expression newExpression) {
		Expression newStruct = structOrUnion.replaceWith(oldExpression,
				newExpression);
		CommonDotExpression result = null;

		if (newStruct != null) {
			result = new CommonDotExpression(this.getSource(), newStruct,
					this.fieldIndex);
		}

		if (result != null)
			result.setExpressionType(expressionType);

		return result;
	}

	@Override
	public Variable variableWritten(Scope scope) {
		if (structOrUnion instanceof LHSExpression) {
			return ((LHSExpression) structOrUnion).variableWritten(scope);
		}
		return null;
	}

	@Override
	public Variable variableWritten() {
		if (structOrUnion instanceof LHSExpression) {
			return ((LHSExpression) structOrUnion).variableWritten();
		}
		return null;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		Set<Variable> variableSet = new HashSet<>();
		Set<Variable> operandResult = structOrUnion.variableAddressedOf(scope);

		if (operandResult != null)
			variableSet.addAll(operandResult);
		return variableSet;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		Set<Variable> variableSet = new HashSet<>();
		Set<Variable> operandResult = structOrUnion.variableAddressedOf();

		if (operandResult != null)
			variableSet.addAll(operandResult);
		return variableSet;
	}

	@Override
	public boolean isStruct() {
		return this.structOrUnion.getExpressionType().isStructType();
	}

	@Override
	public boolean isUnion() {
		return this.structOrUnion.getExpressionType().isUnionType();
	}

	@Override
	public LHSExpressionKind lhsExpressionKind() {
		return LHSExpressionKind.DOT;
	}

}
