package edu.udel.cis.vsl.abc.ast.type.common;

import edu.udel.cis.vsl.abc.ast.type.IF.FloatingType;

public class CommonFloatingType extends CommonBasicType implements FloatingType {

	private static BasicTypeKind floatToBasic(FloatKind floatKind,
			boolean isComplex) {
		if (isComplex) {
			switch (floatKind) {
			case FLOAT:
				return BasicTypeKind.FLOAT_COMPLEX;
			case DOUBLE:
				return BasicTypeKind.DOUBLE_COMPLEX;
			case LONG_DOUBLE:
				return BasicTypeKind.LONG_DOUBLE_COMPLEX;
			case REAL:
				return BasicTypeKind.REAL;
			}
		} else {
			switch (floatKind) {
			case FLOAT:
				return BasicTypeKind.FLOAT;
			case DOUBLE:
				return BasicTypeKind.DOUBLE;
			case LONG_DOUBLE:
				return BasicTypeKind.LONG_DOUBLE;
			case REAL:
				return BasicTypeKind.REAL;
			}
		}
		throw new RuntimeException("Not reachable");
	}

	private FloatKind floatKind;

	private boolean isComplex;

	public CommonFloatingType(FloatKind floatKind, boolean isComplex) {
		super(floatToBasic(floatKind, isComplex));
		this.floatKind = floatKind;
		this.isComplex = isComplex;
	}

	@Override
	public boolean isComplex() {
		return isComplex;
	}

	@Override
	public FloatKind getFloatKind() {
		return floatKind;
	}

}
