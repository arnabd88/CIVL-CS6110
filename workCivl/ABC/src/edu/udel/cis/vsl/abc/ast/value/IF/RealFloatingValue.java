package edu.udel.cis.vsl.abc.ast.value.IF;

import java.math.BigInteger;

import edu.udel.cis.vsl.abc.ast.type.IF.FloatingType;

public interface RealFloatingValue extends Value {

	@Override
	FloatingType getType();

	int getRadix();

	double getDoubleValue();

	BigInteger getWholePartValue();

	BigInteger getFractionPartValue();

	int getFractionLength();

	BigInteger getExponentValue();

}
