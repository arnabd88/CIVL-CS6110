package edu.udel.cis.vsl.civl.model.common.type;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.civl.model.IF.type.CIVLCompleteDomainType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLDomainType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPrimitiveType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicUnionType;

public class CommonDomainType extends CommonType implements CIVLDomainType {

	public final static int classCode = CommonDomainType.class.hashCode();

	private SymbolicUnionType subtypesUnion;

	private CIVLType rangeType;

	public CommonDomainType(CIVLType rangeType) {
		super();
		this.rangeType = rangeType;
	}

	/**
	 * For incomplete domain or literal domain
	 */
	public CommonDomainType() {
		super();
	}

	@Override
	public TypeKind typeKind() {
		return TypeKind.DOMAIN;
	}

	@Override
	public boolean hasState() {
		return false;
	}

	@Override
	public SymbolicType getDynamicType(SymbolicUniverse universe) {
		if (this.dynamicType == null) {
			List<SymbolicType> tupleComponents = new LinkedList<>();
			SymbolicTupleType domainTupleType;
			SymbolicArrayType recDomainType, literalDomainType;
			SymbolicType integerType = universe.integerType();
			SymbolicType rangeType = this.rangeType.getDynamicType(universe);

			recDomainType = universe.arrayType(rangeType);
			literalDomainType = universe.arrayType(universe
					.arrayType(integerType));
			tupleComponents.add(universe.integerType());
			tupleComponents.add(universe.integerType());
			if (this.subtypesUnion == null)
				this.subtypesUnion = universe.unionType(
						universe.stringObject("domain"),
						Arrays.asList(recDomainType, literalDomainType));
			tupleComponents.add(this.subtypesUnion);
			domainTupleType = universe.tupleType(
					universe.stringObject("$domain"), tupleComponents);
			this.dynamicType = domainTupleType;
		}
		return this.dynamicType;
	}

	@Override
	public SymbolicUnionType getDynamicSubTypesUnion(SymbolicUniverse universe) {
		if (this.subtypesUnion == null)
			this.getDynamicType(universe);
		return this.subtypesUnion;
	}

	@Override
	public boolean isDomainType() {
		return true;
	}

	@Override
	public CIVLType copyAs(CIVLPrimitiveType type, SymbolicUniverse universe) {
		return this;
	}

	@Override
	public String toString() {
		return "$domain";
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		return obj instanceof CommonDomainType
				&& !(obj instanceof CIVLCompleteDomainType);
	}

	@Override
	public int hashCode() {
		return classCode;
	}

	@Override
	public boolean isComplete() {
		return (this instanceof CIVLCompleteDomainType);
	}

	@Override
	public boolean areSubtypesScalar() {
		return false;
	}
}
