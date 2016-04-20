package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnionLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLHeapType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLStructOrUnionType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.type.StructOrUnionField;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public class CommonUnionLiteralExpression extends CommonExpression implements
		UnionLiteralExpression {

	private StructOrUnionField memberType;
	private Expression value;

	public CommonUnionLiteralExpression(CIVLSource source,
			StructOrUnionField memberType, Expression value) {
		super(source);
		this.memberType = memberType;
		this.value = value;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.UNION_LITERAL;
	}

	@Override
	public Expression value() {
		// TODO Auto-generated method stub
		return this.value;
	}

	@Override
	public CIVLStructOrUnionType unionType() {
		assert this.expressionType instanceof CIVLStructOrUnionType;
		return (CIVLStructOrUnionType) this.expressionType;
	}

	@Override
	public StructOrUnionField memberType() {
		return this.memberType;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope,
			CIVLHeapType heapType, CIVLType commType) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Set<Variable> variableAddressedOf(CIVLHeapType heapType,
			CIVLType commType) {
		// TODO Auto-generated method stub
		return null;
	}

}
