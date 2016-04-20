package edu.udel.cis.vsl.abc.ast.value.common;

import edu.udel.cis.vsl.abc.ast.type.IF.FloatingType;
import edu.udel.cis.vsl.abc.ast.value.IF.ComplexValue;
import edu.udel.cis.vsl.abc.ast.value.IF.RealFloatingValue;
import edu.udel.cis.vsl.abc.ast.value.IF.ValueFactory.Answer;

public class CommonComplexValue extends CommonValue implements ComplexValue {

	private final static int classCode = CommonComplexValue.class.hashCode();

	private RealFloatingValue realPart;

	private RealFloatingValue imaginaryPart;

	public CommonComplexValue(FloatingType complexType,
			RealFloatingValue realPart, RealFloatingValue imaginaryPart) {
		super(complexType);
		assert realPart != null;
		assert imaginaryPart != null;
		this.realPart = realPart;
		this.imaginaryPart = imaginaryPart;
	}

	@Override
	public RealFloatingValue getRealPart() {
		return realPart;
	}

	@Override
	public RealFloatingValue getImaginaryPart() {
		return imaginaryPart;
	}

	@Override
	public FloatingType getType() {
		return (FloatingType) super.getType();
	}

	@Override
	public boolean equals(Object object) {
		if (this == object)
			return true;
		if (object instanceof CommonComplexValue) {
			CommonComplexValue that = (CommonComplexValue) object;

			return getType().equals(that.getType())
					&& realPart.equals(that.realPart)
					&& imaginaryPart.equals(that.imaginaryPart);
		}
		return false;
	}

	@Override
	public int hashCode() {
		return classCode + getType().hashCode() + realPart.hashCode()
				+ imaginaryPart.hashCode();
	}

	@Override
	public Answer isZero() {
		return realPart.isZero() == Answer.YES
				&& imaginaryPart.isZero() == Answer.YES ? Answer.YES
				: Answer.NO;
	}

	@Override
	public String toString() {
		return "ComplexValue[" + realPart + "," + imaginaryPart + "]";
	}

}
