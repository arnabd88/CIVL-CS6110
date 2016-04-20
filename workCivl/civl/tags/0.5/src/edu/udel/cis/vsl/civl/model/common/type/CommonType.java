package edu.udel.cis.vsl.civl.model.common.type;

import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * Root of CIVL class hierarchy.
 * 
 * @author siegel
 * 
 */
public abstract class CommonType implements CIVLType {

	protected SymbolicType dynamicType = null;

	private int dynamicTypeIndex = -1;

	private Variable stateVariable = null;

	public CommonType() {
	}

	@Override
	public boolean isNumericType() {
		return false;
	}

	@Override
	public boolean isIntegerType() {
		return false;
	}

	@Override
	public boolean isRealType() {
		return false;
	}

	@Override
	public boolean isPointerType() {
		return false;
	}

	@Override
	public boolean isProcessType() {
		return false;
	}

	@Override
	public boolean isScopeType() {
		return false;
	}

	@Override
	public Variable getStateVariable() {
		return stateVariable;
	}

	@Override
	public void setStateVariable(Variable variable) {
		stateVariable = variable;
	}

	@Override
	public boolean isVoidType() {
		return false;
	}

	@Override
	public boolean isHeapType() {
		return false;
	}

	@Override
	public boolean isBundleType() {
		return false;
	}

	@Override
	public boolean isArrayType() {
		return false;
	}

	@Override
	public boolean isStructType() {
		return false;
	}
	
	@Override
	public boolean isCharType() {
		return false;
	}

	@Override
	public int getDynamicTypeIndex() {
		return dynamicTypeIndex;
	}

	public void setDynamicTypeIndex(int index) {
		this.dynamicTypeIndex = index;
	}

}
