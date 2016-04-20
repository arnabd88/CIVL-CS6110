/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.UndefinedProcessExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * Undefined process expression, i.e., a process expression with id -1. Used
 * when translating atomic statements.
 * 
 * @author Manchun Zheng (zheng)
 * 
 */
public class CommonUndefinedProcessExpression extends CommonExpression
		implements UndefinedProcessExpression {

	/**
	 * Self expression. Returns a reference to the process in which the
	 * expression is evaluated.
	 */
	public CommonUndefinedProcessExpression(CIVLSource source, CIVLType type,
			SymbolicExpression constantValue) {
		super(source, null, null, type);
		this.constantValue = constantValue;
	}

	@Override
	public String toString() {
		return "process<-1>";
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.UNDEFINED_PROC;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		return null;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		return null;
	}

	@Override
	protected boolean expressionEquals(Expression expression) {
		return true;
	}
}
