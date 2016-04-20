package edu.udel.cis.vsl.abc.ast.type.IF;

/**
 * The floating types come in four kinds: <code>float</code>,
 * <code>double</code>, <code>long double</code>, representing increasing
 * precision, and "real", a CIVL-C type denoted <code>$real</code> representing
 * the mathematical real numbers. Each also comes in a real and complex variant.
 * 
 * @author siegel
 * 
 */
public interface FloatingType extends StandardBasicType {

	public static enum FloatKind {
		FLOAT, DOUBLE, LONG_DOUBLE, REAL
	};

	/**
	 * Is this complex?
	 * 
	 * @return true if complex, false if real
	 * */
	boolean isComplex();

	/**
	 * The kind of floating type (float, double, or long double).
	 * 
	 * @return the float kind
	 */
	FloatKind getFloatKind();
}
