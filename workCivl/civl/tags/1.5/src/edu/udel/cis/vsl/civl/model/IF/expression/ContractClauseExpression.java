package edu.udel.cis.vsl.civl.model.IF.expression;


public interface ContractClauseExpression extends Expression {
	public enum ContractKind {
		REQUIRES, ENSURES
	};

	boolean isCollectiveClause();

	Expression getCollectiveGroup();

	Expression getBody();

	ContractKind contractKind();

	@Override
	ContractClauseExpression replaceWith(ConditionalExpression oldExpr,
			Expression newExpr);
}
