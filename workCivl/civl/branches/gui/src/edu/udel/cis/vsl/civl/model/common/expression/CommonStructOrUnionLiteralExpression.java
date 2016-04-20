package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.StructOrUnionLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLStructOrUnionType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;

public class CommonStructOrUnionLiteralExpression extends CommonExpression
		implements StructOrUnionLiteralExpression {

	private Expression[] fields;

	public CommonStructOrUnionLiteralExpression(CIVLSource source,
			Scope hscope, Scope lscope, CIVLType type, List<Expression> fields) {
		super(source, hscope, lscope, type);
		this.fields = new Expression[fields.size()];
		fields.toArray(this.fields);
	}

	public CommonStructOrUnionLiteralExpression(CIVLSource source,
			Scope hscope, Scope lscope, CIVLType type,
			SymbolicExpression constantValue) {
		super(source, hscope, lscope, type);
		this.constantValue = constantValue;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.STRUCT_OR_UNION_LITERAL;
	}

	@Override
	public Expression[] fields() {
		return this.fields;
	}

	@Override
	public void setFields(Expression[] fields) {
		this.fields = fields;
	}

	@Override
	public CIVLStructOrUnionType structOrUnionType() {
		assert this.expressionType instanceof CIVLStructOrUnionType;
		return (CIVLStructOrUnionType) this.expressionType;
	}

	@Override
	public String toString() {

		if (this.constantValue == null) {
			String result = "{";
			if (fields != null) {
				CIVLStructOrUnionType structType = this.structOrUnionType();
				String fieldName;
				int i = 0;

				for (Expression field : fields) {
					fieldName = structType.getField(i).name().name();
					i++;
					result += " ." + fieldName + "=" + field + ", ";
				}
				result = result.substring(0, result.length() - 2);
			}
			result += " }";
			return result;
		} else
			return this.constantValue.toString();
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		Set<Variable> result = new HashSet<>();

		if (fields != null) {
			for (Expression field : fields) {
				Set<Variable> elementResult = field.variableAddressedOf(scope);

				if (elementResult != null)
					result.addAll(elementResult);
			}
		}
		return result;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		Set<Variable> result = new HashSet<>();

		if (fields != null) {
			for (Expression field : fields) {
				Set<Variable> elementResult = field.variableAddressedOf();

				if (elementResult != null)
					result.addAll(elementResult);
			}
		}
		return result;
	}

	@Override
	public boolean isStruct() {
		return this.structOrUnionType().isStructType();
	}

	@Override
	public LiteralKind literalKind() {
		return LiteralKind.STRUCT_OR_UNION;
	}

	@Override
	public void calculateConstantValue(SymbolicUniverse universe) {
		List<SymbolicExpression> fieldValues = new ArrayList<>();

		for (Expression field : fields) {
			SymbolicExpression fieldValue = field.constantValue();

			if (fieldValue == null)
				return;
		}
		constantValue = universe.tuple((SymbolicTupleType) this.expressionType
				.getDynamicType(universe), fieldValues);
	}

	@Override
	public void setLiteralConstantValue(SymbolicExpression value) {
		this.constantValue = value;
	}

	@Override
	protected boolean expressionEquals(Expression expression) {
		StructOrUnionLiteralExpression that = (StructOrUnionLiteralExpression) expression;
		int thisFieldLength = this.fields.length;

		if (thisFieldLength == that.fields().length) {
			for (int i = 0; i < thisFieldLength; i++)
				if (!this.fields[i].equals(that.fields()[i]))
					return false;
			return true;
		}
		return false;
	}

	@Override
	public boolean containsHere() {
		for (Expression field : fields) {
			if (field.containsHere())
				return true;
		}
		return false;
	}
}
