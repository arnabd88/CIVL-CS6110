package edu.udel.cis.vsl.civl.model.common.type;

import java.math.BigInteger;
import java.util.Map;

import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLEnumType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPrimitiveType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class CommonEnumType extends CommonType implements CIVLEnumType {

	private String name;
	private Map<String, BigInteger> valueMap;

	public CommonEnumType(String name, Map<String, BigInteger> valueMap,
			SymbolicType dynamicType) {
		this.name = name;
		this.dynamicType = dynamicType;
		this.valueMap = valueMap;
	}

	@Override
	public boolean hasState() {
		return false;
	}

	@Override
	public SymbolicType getDynamicType(SymbolicUniverse universe) {
		if (dynamicType == null)
			throw new CIVLInternalException(
					"no dynamic type specified for primitive enum " + name,
					(CIVLSource) null);
		return dynamicType;
	}

	@Override
	public String name() {
		return this.name;
	}

	@Override
	public BigInteger valueOf(String member) {
		if (!valueMap.containsKey(member))
			throw new CIVLInternalException("no enumerator " + member
					+ " defined in the enumeration type " + name,
					(CIVLSource) null);
		return valueMap.get(member);
	}

	@Override
	public boolean isEnumerationType() {
		return true;
	}

	@Override
	public String toString() {
		String result = "enum ";

		if (name != null)
			result += (name + " ");
		result += "{";
		for (String member : valueMap.keySet()) {
			result += (member + "=" + valueMap.get(member) + ", ");
		}
		result = result.substring(0, result.length() - 2);
		result += "}";
		return result;
	}

	@Override
	public TypeKind typeKind() {
		return TypeKind.ENUM;
	}

	@Override
	public BigInteger firstValue() {
		for (String key : this.valueMap.keySet()) {
			return this.valueMap.get(key);
		}
		return BigInteger.ZERO;
	}

	@Override
	public CIVLType copyAs(CIVLPrimitiveType type, SymbolicUniverse universe) {
		return type;
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof CIVLEnumType)
			return true;
		return false;
	}

	@Override
	public boolean isScalar() {
		return true;
	}

}
