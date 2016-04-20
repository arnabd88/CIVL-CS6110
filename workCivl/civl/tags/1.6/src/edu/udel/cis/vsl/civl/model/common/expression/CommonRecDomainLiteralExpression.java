package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.RecDomainLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLDomainType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;

public class CommonRecDomainLiteralExpression extends CommonExpression
		implements RecDomainLiteralExpression {

	private Expression[] ranges;

	public CommonRecDomainLiteralExpression(CIVLSource source, Scope lscope,
			List<Expression> ranges, CIVLType type) {
		super(source, null, lscope, type);
		this.ranges = new Expression[ranges.size()];
		ranges.toArray(this.ranges);
	}

	@Override
	public LiteralKind literalKind() {
		return LiteralKind.DOMAIN;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.REC_DOMAIN_LITERAL;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		Set<Variable> result = new HashSet<>();

		if (this.ranges != null) {
			for (Expression range : ranges) {
				Set<Variable> rangeResult = range.variableAddressedOf(scope);

				if (rangeResult != null)
					result.addAll(rangeResult);
			}
		}
		return result;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		Set<Variable> result = new HashSet<>();

		if (this.ranges != null) {
			for (Expression range : ranges) {
				Set<Variable> rangeResult = range.variableAddressedOf();

				if (rangeResult != null)
					result.addAll(rangeResult);
			}
		}
		return result;
	}

	@Override
	public Expression rangeAt(int index) {
		return ranges[index];
	}

	@Override
	public int dimension() {
		return ranges.length;
	}

	@Override
	public String toString() {
		StringBuffer string = new StringBuffer();
		int dim = this.dimension();
		boolean first = true;

		string.append("{");
		for (int i = 0; i < dim; i++) {
			if (first)
				first = false;
			else
				string.append(", ");
			string.append(ranges[i]);
		}
		string.append("}");
		return string.toString();
	}

	@Override
	public void calculateConstantValueWork(SymbolicUniverse universe) {
		List<SymbolicExpression> rangeValues = new ArrayList<>();
		List<SymbolicExpression> domValueComponents = new LinkedList<>();
		SymbolicExpression rangesArray;
		CIVLDomainType civlDomType = (CIVLDomainType) this.expressionType;

		for (Expression range : ranges) {
			SymbolicExpression rangeValue;

			range.calculateConstantValue(universe);
			rangeValue = range.constantValue();
			if (rangeValue == null)
				return;
			rangeValues.add(rangeValue);
		}
		// Adding components
		domValueComponents.add(universe.integer(this.dimension()));
		// Union field index which indicates it's a rectangular domain.
		domValueComponents.add(universe.zeroInt());
		rangesArray = universe.array(rangeValues.get(0).type(), rangeValues);
		domValueComponents.add(universe.unionInject(
				civlDomType.getDynamicSubTypesUnion(universe),
				universe.intObject(0), rangesArray));
		// The cast is guaranteed
		this.constantValue = universe.tuple(
				(SymbolicTupleType) civlDomType.getDynamicType(universe),
				domValueComponents);
	}

	@Override
	public void setLiteralConstantValue(SymbolicExpression value) {
		this.constantValue = value;
	}

	@Override
	protected boolean expressionEquals(Expression expression) {
		RecDomainLiteralExpression that = (RecDomainLiteralExpression) expression;
		int thisDim = this.dimension();

		if (thisDim == that.dimension()) {
			for (int i = 0; i < thisDim; i++)
				if (!this.rangeAt(i).equals(that.rangeAt(i)))
					return false;
			return true;
		}

		return false;
	}
}
