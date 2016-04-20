package edu.udel.cis.vsl.civl.model.IF.expression;

public interface DomainLiteralExpression extends LiteralExpression {
	Expression rangeAt(int index);
	
	int dimension();
}
