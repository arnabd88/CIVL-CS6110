/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.UndefinedProcessExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLHeapType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

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
	public CommonUndefinedProcessExpression(CIVLSource source) {
		super(source);
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
