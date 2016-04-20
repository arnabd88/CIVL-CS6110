package edu.udel.cis.vsl.civl.model.common.type;

import java.util.ArrayList;
import java.util.List;

import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLDomainType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class CommonDomainType extends CommonType implements CIVLDomainType {

	private int dimension;
	private CIVLType rangeType;
	private SymbolicTupleType dynamicType = null;

	public CommonDomainType(CIVLType rangeType, int dim,
			SymbolicUniverse universe) {
		this.dimension = dim;
		this.rangeType = rangeType;
	}

	public CommonDomainType(SymbolicUniverse universe) {
		this.dimension = -1;
	}

	@Override
	public boolean hasState() {
		return false;
	}

	@Override
	public SymbolicType getDynamicType(SymbolicUniverse universe) {
		if (dynamicType != null)
			return this.dynamicType;
		if (this.dimension < 1)
			throw new CIVLInternalException(
					"no dynamic type for non-dimension $domain type: "
							+ toString(), (CIVLSource) null);
		else {
			List<SymbolicType> rangeTypes = new ArrayList<>(this.dimension);
			SymbolicType symbolicRangeType = rangeType.getDynamicType(universe);

			for (int i = 0; i < dimension; i++) {
				rangeTypes.add(symbolicRangeType);
			}
			dynamicType = universe.tupleType(
					universe.stringObject(this.toString()), rangeTypes);
			return dynamicType;
		}
	}

	@Override
	public int dimension() {
		return this.dimension;
	}

	@Override
	public String toString() {
		if (this.dimension == -1)
			return "$domain";
		else
			return "$domain(" + this.dimension + ")";
	}

	@Override
	public boolean isDomainType() {
		return true;
	}

	@Override
	public CIVLType rangeType() {
		return this.rangeType;
	}

	@Override
	public TypeKind typeKind() {
		return TypeKind.DOMAIN;
	}
}
