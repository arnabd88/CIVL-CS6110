package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.StructOrUnionLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLStructOrUnionType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public class CommonStructOrUnionLiteralExpression extends CommonExpression
		implements StructOrUnionLiteralExpression {

	private Expression[] fields;

	public CommonStructOrUnionLiteralExpression(CIVLSource source,
			CIVLType type, ArrayList<Expression> fields) {
		super(source);
		this.fields = new Expression[fields.size()];
		fields.toArray(this.fields);
		this.setExpressionType(type);
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
}
