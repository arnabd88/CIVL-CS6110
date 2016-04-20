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
import edu.udel.cis.vsl.civl.model.IF.type.CIVLHeapType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * @author zirkel
 * 
 */
public class CommonDotExpression extends CommonExpression implements
		DotExpression {

	private Expression struct;// TODO shall this be of type LHSExpression?
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
		this.struct = struct;
		this.fieldIndex = fieldIndex;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see edu.udel.cis.vsl.civl.model.IF.expression.DotExpression#struct()
	 */
	@Override
	public Expression struct() {
		return struct;
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
		return struct.toString() + "." + fieldIndex;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.DOT;
	}

	@Override
	public void calculateDerefs() {
		this.struct.calculateDerefs();
		this.hasDerefs = this.struct.hasDerefs();
	}

	@Override
	public void setPurelyLocal(boolean pl) {
		// TODO what if &(a.index) where a is defined as a struct
		// and index is a field of the struct
	}

	@Override
	public void purelyLocalAnalysisOfVariables(Scope funcScope) {
		this.struct.purelyLocalAnalysisOfVariables(funcScope);
	}

	@Override
	public void purelyLocalAnalysis() {
		if (this.hasDerefs) {
			this.purelyLocal = false;
			return;
		}

		this.struct.purelyLocalAnalysis();
		this.purelyLocal = this.struct.isPurelyLocal();
	}

	@Override
	public void replaceWith(ConditionalExpression oldExpression,
			VariableExpression newExpression) {
		if (struct == oldExpression) {
			struct = newExpression;
			return;
		}
		struct.replaceWith(oldExpression, newExpression);
	}

	@Override
	public Expression replaceWith(ConditionalExpression oldExpression,
			Expression newExpression) {
		Expression newStruct = struct.replaceWith(oldExpression, newExpression);
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
	public Variable variableWritten(Scope scope, CIVLHeapType heapType,
			CIVLType commType) {
		if (struct instanceof LHSExpression) {
			return ((LHSExpression) struct).variableWritten(scope, heapType,
					commType);
		}
		return null;
	}

	@Override
	public Variable variableWritten(CIVLHeapType heapType, CIVLType commType) {
		if (struct instanceof LHSExpression) {
			return ((LHSExpression) struct).variableWritten(heapType, commType);
		}
		return null;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope,
			CIVLHeapType heapType, CIVLType commType) {
		Set<Variable> variableSet = new HashSet<>();
		Set<Variable> operandResult = struct.variableAddressedOf(scope,
				heapType, commType);

		if (operandResult != null)
			variableSet.addAll(operandResult);
		return variableSet;
	}

	@Override
	public Set<Variable> variableAddressedOf(CIVLHeapType heapType,
			CIVLType commType) {
		Set<Variable> variableSet = new HashSet<>();
		Set<Variable> operandResult = struct.variableAddressedOf(heapType,
				commType);

		if (operandResult != null)
			variableSet.addAll(operandResult);
		return variableSet;
	}

}
