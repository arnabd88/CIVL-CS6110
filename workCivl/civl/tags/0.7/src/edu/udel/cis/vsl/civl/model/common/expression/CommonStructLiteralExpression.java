package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.StructLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLHeapType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLStructOrUnionType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public class CommonStructLiteralExpression extends CommonExpression implements
		StructLiteralExpression {

	private Expression[] fields;

	public CommonStructLiteralExpression(CIVLSource source, CIVLType type,
			ArrayList<Expression> fields) {
		super(source);
		this.fields = new Expression[fields.size()];
		fields.toArray(this.fields);
		this.setExpressionType(type);
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.STRUCT_LITERAL;
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
	public CIVLStructOrUnionType structType() {
		assert this.expressionType instanceof CIVLStructOrUnionType;
		return (CIVLStructOrUnionType) this.expressionType;
	}

	@Override
	public String toString() {
		String result = "{";
		if (fields != null) {
			CIVLStructOrUnionType structType = this.structType();
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
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope,
			CIVLHeapType heapType, CIVLType commType) {
		Set<Variable> result = new HashSet<>();

		if (fields != null) {
			for (Expression field : fields) {
				Set<Variable> elementResult = field.variableAddressedOf(scope,
						heapType, commType);

				if (elementResult != null)
					result.addAll(elementResult);
			}
		}
		return result;
	}

	@Override
	public Set<Variable> variableAddressedOf(CIVLHeapType heapType,
			CIVLType commType) {
		Set<Variable> result = new HashSet<>();

		if (fields != null) {
			for (Expression field : fields) {
				Set<Variable> elementResult = field.variableAddressedOf(
						heapType, commType);

				if (elementResult != null)
					result.addAll(elementResult);
			}
		}
		return result;
	}
}
