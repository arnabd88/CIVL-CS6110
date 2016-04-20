package edu.udel.cis.vsl.abc.ast.value.common;

import java.math.BigInteger;

import edu.udel.cis.vsl.abc.ast.type.IF.IntegerType;
import edu.udel.cis.vsl.abc.ast.value.IF.ValueFactory.Answer;

/**
 * An instance of this class represents an integer value that results from
 * mapping a mathematical integer into an integer type. The Standard specifies
 * that for unsigned integer types, the mathematical integer will be reduced
 * modulo MAX+1 (where MAX is the largest value representable in that type). For
 * unsigned types, if the mathematical integer does not fit into the range of
 * the type, the behavior is undefined.
 * 
 * @author siegel
 * 
 */
public class MappedIntegerValue extends CommonValue {

	private final static int classCode = MappedIntegerValue.class.hashCode();

	private BigInteger intValue;

	public MappedIntegerValue(IntegerType type, BigInteger intValue) {
		super(type);
		this.intValue = intValue;
	}

	@Override
	public Answer isZero() {
		return Answer.MAYBE;
	}

	public BigInteger getIntValue() {
		return intValue;
	}

	@Override
	public String toString() {
		return "(" + getType() + ")" + intValue;
	}

	@Override
	public int hashCode() {
		return classCode + getType().hashCode() + intValue.hashCode();
	}

}
