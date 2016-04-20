package edu.udel.cis.vsl.civl.model.common.type;

import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * Root of CIVLType class hierarchy.
 * 
 * @author siegel
 * 
 */
public abstract class CommonType implements CIVLType {

	protected SymbolicType dynamicType = null;

	/**
	 * CIVL associates a single dynamic type to every CIVL type and does this
	 * once at compile time. All the dynamic types which occur as dynamic types
	 * of CIVL types are numbered from 0. This is used in particular to
	 * construct the bundle type which is the union of all of the dynamic types.
	 * This field is the dynamic type index to this one and it's initially be
	 * minus one and can be set later by calling
	 * {@link #setDynamicTypeIndex(int)} and the getter is
	 * {@link #getDynamicTypeIndex()}
	 */
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
	public boolean isUnionType() {
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

	@Override
	public boolean isHandleType() {
		return false;
	}

	@Override
	public boolean isHandleObjectType() {
		return false;
	}

	/**
	 * 
	 * Sets the dynamic type index for this CIVL type. CIVL associates a single
	 * dynamic type to every CIVL type and does this once at compile time. All
	 * the dynamic types which occur as dynamic types of CIVL types are numbered
	 * from 0. This is used in particular to construct the bundle type which is
	 * the union of all of the dynamic types. This field is the dynamic type
	 * index to this one and it's initially be minus one and can be set later by
	 * calling this method and the getter is {@link #getDynamicTypeIndex()}.
	 * 
	 * @param index
	 *            the dynamic type index of this CIVL type
	 */
	public void setDynamicTypeIndex(int index) {
		this.dynamicTypeIndex = index;
	}

	@Override
	public boolean isEnumerationType() {
		return false;
	}

	@Override
	public boolean isBoolType() {
		return false;
	}

	@Override
	public boolean isDomainType() {
		return false;
	}

	@Override
	public boolean isIncompleteArrayType() {
		return false;
	}

	@Override
	public boolean isSuperTypeOf(CIVLType subtype) {
		return this.equals(subtype);
	}
}
