package edu.udel.cis.vsl.civl.model.common.type;

import edu.udel.cis.vsl.civl.model.IF.type.CIVLCompleteDomainType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;

public class CommonCompleteDomainType extends CommonDomainType implements
		CIVLCompleteDomainType {

	public final static int classCode = CommonCompleteDomainType.class
			.hashCode();

	private int dimension;

	public CommonCompleteDomainType(CIVLType rangeType, int dimension) {
		super(rangeType);
		assert dimension >= 1 : "For complete domain type, dimension must be greater than 0";
		this.dimension = dimension;
	}

	@Override
	public int getDimension() {
		return dimension;
	}

	@Override
	public String toString() {
		return "$domain(" + dimension + ")";
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj instanceof CommonCompleteDomainType) {
			return dimension == ((CommonCompleteDomainType) obj).dimension;
		}
		return false;
	}

	@Override
	public int hashCode() {
		return classCode ^ dimension;
	}

	@Override
	public boolean isDomainType() {
		return true;
	}
}
