package edu.udel.cis.vsl.civl.model.common.statement;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.CivlParForEnterStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLCompleteDomainType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;

public class CommonCivlParForEnterStatement extends CommonStatement implements
		CivlParForEnterStatement {

	private Expression domain;

	private VariableExpression domSizeVar;

	private Expression parProcsPointer;

	private VariableExpression parProcsVar;

	private CIVLFunction parProcFunction;

	public CommonCivlParForEnterStatement(CIVLSource source, Location start,
			Expression guard, Expression domain, VariableExpression domSize,
			VariableExpression parProcsVar, Expression parProcs,
			CIVLFunction parProcFunc) {
		super(source, domain.expressionScope(), start, guard);
		this.domain = domain;
		this.domSizeVar = domSize;
		this.parProcsVar = parProcsVar;
		this.parProcsPointer = parProcs;
		this.parProcFunction = parProcFunc;
	}

	@Override
	public Statement replaceWith(ConditionalExpression oldExpression,
			Expression newExpression) {
		return null;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		return domain.variableAddressedOf(scope);
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		return domain.variableAddressedOf();
	}

	@Override
	public StatementKind statementKind() {
		return StatementKind.CIVL_PAR_FOR_ENTER;
	}

	@Override
	public CIVLFunction parProcFunction() {
		return this.parProcFunction;
	}

	@Override
	public Expression domain() {
		return this.domain;
	}

	@Override
	public VariableExpression domSizeVar() {
		return this.domSizeVar;
	}

	@Override
	public Expression parProcsPointer() {
		return this.parProcsPointer;
	}

	@Override
	public String toString() {
		StringBuilder string = new StringBuilder();

		string.append("CIVL_PAR_FOR_ENTER: ");
		string.append("$spawn ");
		string.append(this.parProcFunction.name().name());
		string.append("() : ");
		string.append(this.domain);
		return string.toString();
	}

	@Override
	public int dimension() {
		return ((CIVLCompleteDomainType) this.domain.getExpressionType())
				.getDimension();
	}

	@Override
	public VariableExpression parProcsVar() {
		return this.parProcsVar;
	}

	@Override
	protected void calculateConstantValueWork(SymbolicUniverse universe) {
		this.domain.calculateConstantValue(universe);
	}
}
