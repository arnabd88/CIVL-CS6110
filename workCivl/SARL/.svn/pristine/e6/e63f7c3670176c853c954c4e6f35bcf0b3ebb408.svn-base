/**
 * <p>
 * The ideal module supports reasoning about numerical expressions using "ideal"
 * mathematical reals and integers. In particular, addition and multiplication
 * are commutative and associative, there are no finite bounds on these sets,
 * there is no rounding, etc.
 * </p>
 * 
 * <p>
 * The entry point is {@link edu.udel.cis.vsl.sarl.ideal.IF.Ideal Ideal2}.
 * That class provides static methods to get a new
 * {@link edu.udel.cis.vsl.sarl.ideal.IF.IdealFactory Ideal2Factory}, an
 * implementation of
 * {@link edu.udel.cis.vsl.sarl.expr.IF.NumericExpressionFactory}. It also
 * provides a method to get a simplifier factory.
 * </p>
 * 
 * <p>
 * This package provides the interface for the ideal module. All code outside of
 * this module should use only elements provided in this package.
 * </p>
 * 
 * <p>
 * The implementation classes for ideal symbolic expressions and their
 * arithmetic are in package {@link edu.udel.cis.vsl.sarl.ideal.common}.
 * </p>
 * 
 * <p>
 * Package {edu.udel.cis.vsl.sarl.ideal2.simplify} contains the classes
 * implementing a simplifier for ideal expressions.
 * </p>
 * 
 * <p>
 * The interfaces in this package define a simple hierarchy of numeric
 * expressions:
 * <ul>
 * <li>{@link edu.udel.cis.vsl.sarl.ideal.IF.Constant Constant}. As you would
 * expect, a constant is a concrete number, like "5" or "3.1415".</li>
 * <li>{@link edu.udel.cis.vsl.sarl.ideal.IF.Primitive Primitive}. A primitive
 * is a numeric symbolic constant or any other expression which will not be
 * decomposed and therefore plays the role of a single "variable" in a
 * polynomial</li>
 * <li>{@link edu.udel.cis.vsl.sarl.ideal.IF.PrimitivePower PrimitivePower}. A
 * power of a primitive. Note that a primitive p is a primitive power, since it
 * can be expressed as p^1.</li>
 * <li>{@link edu.udel.cis.vsl.sarl.ideal.IF.Monic Monic}. A monic is a product
 * of primitive powers. Note that a primitive power is a monic. The number "1"
 * is also a monic: it is the empty monic (empty product).</li>
 * <li>{@link edu.udel.cis.vsl.sarl.ideal.IF.Monomial Monomial}. A monomial is
 * a product of a constant and a monic. A monic is a monomial (with constant 1).
 * A constant is a monomial (with empty monic).</li>
 * <li>{@link edu.udel.cis.vsl.sarl.ideal.IF.Polynomial Polynomial}. A
 * polynomial is the sum of monomials. It is also a primitive.</li>
 * <li>{@link edu.udel.cis.vsl.sarl.ideal.IF.RationalExpression
 * RationalExpression}. A rational expression is the quotient of two monomials.
 * A monomial is a rational expressions (with denominator 1). A rational
 * expression must have real type. All expressions of integer type are
 * monomials.</li>
 * </ul>
 * </p>
 */
package edu.udel.cis.vsl.sarl.ideal.IF;