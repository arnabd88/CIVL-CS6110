package edu.udel.cis.vsl.civl.model.IF.expression;

public interface DereferenceExpression extends LHSExpression {

	/**
	 * Returns the sole argument of this dereference expression. This is an
	 * expression of pointer type.
	 * 
	 * @return the argument of the dereference operator
	 */
	Expression pointer();

}
