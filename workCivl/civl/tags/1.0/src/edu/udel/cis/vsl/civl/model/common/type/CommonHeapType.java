/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.type;

import java.util.Collection;

import edu.udel.cis.vsl.civl.model.IF.statement.MallocStatement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLHeapType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPrimitiveType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class CommonHeapType extends CommonType implements CIVLHeapType {

	private String name;

	private MallocStatement[] mallocs = null;

	private SymbolicExpression initialValue = null;

	private SymbolicExpression undefinedValue = null;

	public CommonHeapType(String name) {
		this.name = name;
	}

	@Override
	public boolean hasState() {
		return false;
	}

	@Override
	public SymbolicType getDynamicType(SymbolicUniverse universe) {
		return dynamicType;
	}

	@Override
	public int getNumMallocs() {
		return mallocs.length;
	}

	@Override
	public MallocStatement getMalloc(int index) {
		return mallocs[index];
	}

	@Override
	public boolean isComplete() {
		return mallocs != null;
	}

	@Override
	public void complete(Collection<MallocStatement> mallocs,
			SymbolicType dynamicType, SymbolicExpression initialValue,
			SymbolicExpression undefinedValue) {
		this.mallocs = mallocs.toArray(new MallocStatement[mallocs.size()]);
		this.dynamicType = dynamicType;
		this.initialValue = initialValue;
		this.undefinedValue = undefinedValue;
	}

	@Override
	public boolean isHeapType() {
		return true;
	}

	@Override
	public String toString() {
		return "__heap__";
	}

	@Override
	public SymbolicExpression getInitialValue() {
		return initialValue;
	}

	@Override
	public SymbolicExpression getUndefinedValue() {
		return undefinedValue;
	}

	@Override
	public String getName() {
		return name;
	}

	@Override
	public boolean isHandleObjectType() {
		return true;
	}

	@Override
	public TypeKind typeKind() {
		return TypeKind.HEAP;
	}

	@Override
	public CIVLType copyAs(CIVLPrimitiveType type, SymbolicUniverse universe) {
		return this;
	}
}
