/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.type;

import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Map;

import edu.udel.cis.vsl.civl.model.IF.type.CIVLBundleType;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicUnionType;

public class CommonBundleType extends CommonType implements CIVLBundleType {

	private SymbolicType[] elementTypes = null;

	private Map<SymbolicType, Integer> indexMap = null;

	public CommonBundleType() {
	}

	@Override
	public boolean hasState() {
		return false;
	}

	@Override
	public SymbolicUnionType getDynamicType(SymbolicUniverse universe) {
		return (SymbolicUnionType) dynamicType;
	}

	@Override
	public int getNumTypes() {
		return elementTypes.length;
	}

	@Override
	public SymbolicType getElementType(int index) {
		return elementTypes[index];
	}

	@Override
	public boolean isComplete() {
		return elementTypes != null;
	}

	@Override
	public void complete(Collection<SymbolicType> elementTypes,
			SymbolicUnionType dynamicType) {
		int n = elementTypes.size();

		this.elementTypes = elementTypes.toArray(new SymbolicType[n]);
		this.dynamicType = dynamicType;
		this.indexMap = new LinkedHashMap<SymbolicType, Integer>(n);
		for (int i = 0; i < n; i++)
			indexMap.put(this.elementTypes[i], i);
	}

	@Override
	public boolean isBundleType() {
		return true;
	}

	@Override
	public String toString() {
		return "$bundle";
	}

	@Override
	public Integer getIndexOf(SymbolicType elementType) {
		return indexMap.get(elementType);
	}

}
