/*******************************************************************************
 * Copyright (c) 2013 Stephen F. Siegel, University of Delaware.
 * 
 * This file is part of SARL.
 * 
 * SARL is free software: you can redistribute it and/or modify it under the
 * terms of the GNU Lesser General Public License as published by the Free
 * Software Foundation, either version 3 of the License, or (at your option) any
 * later version.
 * 
 * SARL is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
 * A PARTICULAR PURPOSE. See the GNU Lesser General Public License for more
 * details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with SARL. If not, see <http://www.gnu.org/licenses/>.
 ******************************************************************************/
package edu.udel.cis.vsl.sarl.ideal.common;

import java.util.Comparator;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.sarl.IF.SARLException;
import edu.udel.cis.vsl.sarl.IF.SARLInternalException;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.IF.number.RationalNumber;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.object.NumberObject;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject.SymbolicObjectKind;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.expr.IF.BooleanExpressionFactory;
import edu.udel.cis.vsl.sarl.ideal.IF.Constant;
import edu.udel.cis.vsl.sarl.ideal.IF.IdealFactory;
import edu.udel.cis.vsl.sarl.ideal.IF.Monic;
import edu.udel.cis.vsl.sarl.ideal.IF.Monomial;
import edu.udel.cis.vsl.sarl.ideal.IF.Polynomial;
import edu.udel.cis.vsl.sarl.ideal.IF.Primitive;
import edu.udel.cis.vsl.sarl.ideal.IF.PrimitivePower;
import edu.udel.cis.vsl.sarl.ideal.IF.RationalExpression;
import edu.udel.cis.vsl.sarl.object.IF.ObjectFactory;
import edu.udel.cis.vsl.sarl.type.IF.SymbolicTypeFactory;
import edu.udel.cis.vsl.sarl.util.KeySetFactory;

/**
 * <p>
 * An implementation of {@link IdealFactory}. Several of the classes used to
 * represent expressions start with the letters "NT", which stands for
 * "non-trivial". For example {@link NTConstant} implements {@link Constant} and
 * represents any non-trivial constant, i.e., a constant which is not 1.
 * </p>
 * 
 * @author Stephen F. Siegel
 */
public class CommonIdealFactory implements IdealFactory {

	/**
	 * Print debugging information.
	 */
	public final static boolean debug = false;

	/**
	 * The number factory used by this ideal factory to create and manipulate
	 * infinite-precision concrete integer and rational numbers, instances of
	 * {@link Number}, {@link IntegerNumber}, and {@link RationalNumber}.
	 */
	private NumberFactory numberFactory;

	/**
	 * The boolean expression factory used by this ideal factory to create and
	 * manipulate boolean expressions, instances of {@link BooleanExpression}
	 */
	private BooleanExpressionFactory booleanFactory;

	/**
	 * The object factory used by this ideal factory to manipulate symbolic
	 * objects, instances of {@link SymbolicObject}.
	 */
	private ObjectFactory objectFactory;

	/**
	 * The symbolic type factory used by this ideal factory to create and
	 * manipulate symbolic types, instances of {@link SymbolicType}.
	 */
	private SymbolicTypeFactory typeFactory;

	/**
	 * Factory used to maintain sets of {@link PrimitivePower} objects indexed
	 * by their {@link Primitive}s. A {@link Monic} is a product of
	 * {@link PrimitivePower}s and this factory is used to manipulate
	 * {@link Monic}s.
	 */
	private KeySetFactory<Primitive, PrimitivePower> monicFactory;

	/**
	 * Factory used to maintain sets of {@link Monomial} objects indexed by
	 * their {@link Monic}s. A {@link Polynomial} is a sum of {@link Monomial}s
	 * and this factory is used to manipulate {@lik Polynomial}s.
	 */
	private KeySetFactory<Monic, Monomial> polynomialFactory;

	/**
	 * The object used to compare ideal symbolic expressions and thereby place a
	 * total order on them.
	 */
	private IdealComparator comparator;

	/**
	 * A comparator for {@link Monic}s only. It is equivalent to restricting
	 * {@link #comparator} to {@link Monic}s, but may be more efficient.
	 */
	private Comparator<Monic> monicComparator;

	/**
	 * A comparator for {@link Primitive}s only. It is equivalent to restricting
	 * {@link #comparator} to {@link Primitive}s only, but may be more
	 * efficient.
	 */
	private Comparator<Primitive> primitiveComparator;

	/**
	 * The (ideal mathematical) integer type.
	 */
	private SymbolicType integerType;

	/**
	 * The (ideal mathematical) real type.
	 */
	private SymbolicType realType;

	/**
	 * The integer 1, which in the ideal factory is represented as an instance
	 * of {@link One}. A special class is needed here because 1 is both a
	 * {@link Constant} and a {@link Monic} (the empty monic).
	 */
	private One oneInt;

	/**
	 * The real number 1, which in the ideal factory is represented as an
	 * instance of {@link One}. A special class is needed here because 1 is both
	 * a {@link Constant} and a {@link Monic} (the empty monic).
	 */
	private One oneReal;

	/**
	 * The {@link IntObject} wrapping the Java int 1.
	 */
	private IntObject oneIntObject;

	/**
	 * The integer 0 as a symbolic expression, which in this ideal universe is
	 * an instance of {@link Constant}.
	 */
	private Constant zeroInt;

	/**
	 * The integer -1 as a symbolic expression, which in this ideal universe is
	 * an instance of {@link Constant}.
	 */
	private Constant negOneInt;

	/**
	 * The real number 0 as a symbolic expression, which in this ideal universe
	 * is an instance of {@link Constant}.
	 */
	private Constant zeroReal;

	/**
	 * The set of {@link Monomial}s consisting of the single element which is
	 * the integer 1.
	 */
	private Monomial[] oneTermListInt;

	/**
	 * The set of {@link Monomial}s consisting of the single element which is
	 * the real number 1.
	 */
	private Monomial[] oneTermListReal;

	/**
	 * The boolean symbolic expression "true".
	 */
	private BooleanExpression trueExpr;

	/**
	 * The boolean symbolic expression "false".
	 */
	private BooleanExpression falseExpr;

	/**
	 * An object used to add two monomials over the same monic.
	 */
	private MonomialAdder monomialAdder;

	/**
	 * An object used to multiply two primitive powers over the same primitive
	 * base.
	 */
	private PrimitivePowerMultiplier primitivePowerMultiplier;

	/**
	 * The monic factory, a key set factory in which the values are
	 * {@link PrimitivePower}s and the key is obtained by taking the
	 * {@link Primitive} base of the {@link PrimitivePower}.
	 * 
	 * @author siegel
	 */
	private class MonicFactory
			extends KeySetFactory<Primitive, PrimitivePower> {

		MonicFactory(Comparator<Primitive> primitiveComparator) {
			super(primitiveComparator);
		}

		@Override
		protected PrimitivePower[] newSet(int size) {
			return new PrimitivePower[size];
		}

		@Override
		protected Primitive key(PrimitivePower value) {
			return value.primitive(CommonIdealFactory.this);
		}
	};

	/**
	 * The polynomial factory, a key set factory in which the values are
	 * {@link Monomial}s and the key is obtained by taking the {@link Monic} of
	 * the {@link Monomial}.
	 * 
	 * @author siegel
	 */
	private class PolynomialFactory extends KeySetFactory<Monic, Monomial> {

		PolynomialFactory(Comparator<Monic> monicComparator) {
			super(monicComparator);
		}

		@Override
		protected Monomial[] newSet(int size) {
			return new Monomial[size];
		}

		@Override
		protected Monic key(Monomial value) {
			return value.monic(CommonIdealFactory.this);
		}
	};

	/**
	 * Constructs new factory based on the given factories.
	 * 
	 * @param numberFactory
	 *            the number factory used by this ideal factory to create and
	 *            manipulate infinite-precision concrete integer and rational
	 *            numbers, instances of {@link Number}, {@link IntegerNumber},
	 *            and {@link RationalNumber}
	 * @param objectFactory
	 *            the object factory used by this ideal factory to manipulate
	 *            symbolic objects, instances of {@link SymbolicObject}.
	 * @param typeFactory
	 *            the symbolic type factory used by this ideal factory to create
	 *            and manipulate symbolic types, instances of
	 *            {@link SymbolicType}
	 * @param booleanFactory
	 *            the boolean expression factory used by this ideal factory to
	 *            create and manipulate boolean expressions, instances of
	 *            {@link BooleanExpression}
	 */
	public CommonIdealFactory(NumberFactory numberFactory,
			ObjectFactory objectFactory, SymbolicTypeFactory typeFactory,
			BooleanExpressionFactory booleanFactory) {
		this.numberFactory = numberFactory;
		this.objectFactory = objectFactory;
		this.typeFactory = typeFactory;
		this.booleanFactory = booleanFactory;
		this.trueExpr = booleanFactory.trueExpr();
		this.falseExpr = booleanFactory.falseExpr();
		this.comparator = new IdealComparator(this);
		this.monicComparator = new MonicComparator(this.comparator);
		this.primitiveComparator = new PrimitiveComparator(this.comparator);
		this.integerType = typeFactory.integerType();
		this.realType = typeFactory.realType();
		this.oneIntObject = objectFactory.oneIntObj();
		this.oneInt = objectFactory.canonic(new One(integerType,
				objectFactory.numberObject(numberFactory.oneInteger())));
		this.oneReal = objectFactory.canonic(new One(realType,
				objectFactory.numberObject(numberFactory.oneRational())));
		this.zeroInt = canonicIntConstant(0);
		this.negOneInt = canonicIntConstant(-1);
		this.zeroReal = canonicRealConstant(0);
		this.oneTermListInt = new Monomial[] { oneInt };
		this.oneTermListReal = new Monomial[] { oneReal };
		this.monomialAdder = new MonomialAdder(this);
		this.primitivePowerMultiplier = new PrimitivePowerMultiplier(this);
		this.monicFactory = new MonicFactory(primitiveComparator);
		this.polynomialFactory = new PolynomialFactory(monicComparator);
	}

	// ************************** Private Methods *************************

	// Constants...

	/**
	 * Returns the canonic {@link Constant} of integer type with the value
	 * specified.
	 * 
	 * @param value
	 *            any Java <code>int</code>
	 * @return the canonic integer {@link Constant} wrapping that value
	 */
	private Constant canonicIntConstant(int value) {
		return objectFactory.canonic(intConstant(value));
	}

	/**
	 * Returns a {@link Constant} of real type with value the given integer.
	 * 
	 * @param value
	 *            any Java <code>int</code>
	 * @return a real {@link Constant} wrapping that value
	 */
	private Constant realConstant(int value) {
		if (value == 1)
			return oneReal;
		return new NTConstant(realType, objectFactory.numberObject(
				numberFactory.integerToRational(numberFactory.integer(value))));
	}

	/**
	 * Returns the canonic {@link Constant} of real type with value the given
	 * integer.
	 * 
	 * @param value
	 *            any Java <code>int</code>
	 * @return the canonic real {@link Constant} wrapping that value
	 */
	private Constant canonicRealConstant(int value) {
		return objectFactory.canonic(realConstant(value));
	}

	/**
	 * Returns a {@link Constant} wrapping the given number object. The constant
	 * will have either integer or real type, depending on the kind of the
	 * number object.
	 * 
	 * @param object
	 *            any number object
	 * @return an instance of {@link Constant} corresponding to that number
	 */
	private Constant constant(NumberObject object) {
		if (object.isOne())
			return object.isInteger() ? oneInt : oneReal;
		return new NTConstant(object.isInteger() ? integerType : realType,
				object);
	}

	/**
	 * Negates a constant <i>c</i>.
	 * 
	 * @param constant
	 *            a non-<code>null</code> instance of {@link Constant}
	 * @return -<i>c</i>
	 */
	private Constant negate(Constant constant) {
		return constant(objectFactory
				.numberObject(numberFactory.negate(constant.number())));
	}

	/**
	 * Multiplies two constants.
	 * 
	 * @param c1
	 *            a non-<code>null</code> instance of {@link Constant}
	 * @param c2
	 *            a non-<code>null</code> instance of {@link Constant} of the
	 *            same type as <code>c1</code>
	 * @return the product c1*c2
	 */
	private Constant multiplyConstants(Constant c1, Constant c2) {
		return constant(objectFactory.numberObject(
				numberFactory.multiply(c1.number(), c2.number())));
	}

	/**
	 * Divides two constants. The constants must have the same type. If the type
	 * is integer, integer division is performed.
	 * 
	 * @param c1
	 *            a constant
	 * @param c2
	 *            a constant of the same type as c1
	 * @return the constant c1/c2
	 */
	private Constant divideConstants(Constant c1, Constant c2) {
		return constant(objectFactory
				.numberObject(numberFactory.divide(c1.number(), c2.number())));
	}

	/**
	 * Performs integer division of two integer constants.
	 * 
	 * @param c1
	 *            a non-<code>null</code> constant of integer type
	 * @param c2
	 *            a non-<code>null</code> non-0 constant of integer type
	 * @return the result of integer division c1/c2
	 */
	private Constant intDivideConstants(Constant c1, Constant c2) {
		return constant(numberFactory.divide((IntegerNumber) c1.number(),
				(IntegerNumber) c2.number()));
	}

	/**
	 * Computes the integer modulus of two integer constants.
	 * 
	 * @param c1
	 *            a non-<code>null</code> constant of integer type
	 * @param c2
	 *            a non-<code>null</code> non-0 constant of integer type
	 * @return the result of integer modulus c1%c2
	 */
	private Constant intModuloConstants(Constant c1, Constant c2) {
		return constant(numberFactory.mod((IntegerNumber) c1.number(),
				(IntegerNumber) c2.number()));
	}

	// Primitives...

	// Primitive Powers...

	/**
	 * Constructs a non-trivial primitive power with given base and exponent.
	 * 
	 * @param primitive
	 *            a non-<code>null</code> instance of {@link Primitive} which
	 *            will be the base in the new primitive power expression
	 * @param exponent
	 *            the exponent in the new expression, which must be an integer
	 *            greater than or equal to 2
	 * @return the non-trivial primitive power as specified
	 */
	private NTPrimitivePower ntPrimitivePower(Primitive primitive,
			IntObject exponent) {
		return new NTPrimitivePower(primitive, exponent);
	}

	// Monics...

	/**
	 * Constructs a non-trivial monic.
	 * 
	 * @param type
	 *            either the integer or the real type
	 * @param factorSet
	 *            a monic map with at least two entries; this maps a primitive
	 *            to a power of that primitive; all keys and values must have
	 *            type consistent with <code>type</code>
	 * @return the monic which represents the product of the values of the
	 *         <code>monicMap</code>
	 */
	private NTMonic ntMonic(SymbolicType type, PrimitivePower[] factorSet) {
		return new NTMonic(type, factorSet);
	}

	/**
	 * Multiplies two {@link Monic}s.
	 * 
	 * @param monic1
	 *            a non-<code>null</code> {@link Monic}
	 * @param monic2
	 *            a non-<code>null</code> {@link Monic} of the same type as
	 *            <code>monic1</code>
	 * @return the product of the two monics
	 */
	private Monic multiplyMonics(Monic monic1, Monic monic2) {
		return monic(monic1.type(),
				monicFactory.combine(primitivePowerMultiplier,
						monic1.monicFactors(this), monic2.monicFactors(this)));
	}

	/**
	 * Extracts the common factors from two monics. Given monics m1 and m2, this
	 * computes the monic p such that: f1=p*g1, f2=p*g2, and g1 and g2 have no
	 * primitives in common.
	 * 
	 * @param monic1
	 *            a non-<code>null</code> monic
	 * @param monic2
	 *            a monic of same type as <code>m1</code>
	 * @return array of length 3 consisting of p, g1, and g2, in that order
	 */
	private Monic[] extractCommonality(Monic monic1, Monic monic2) {
		SymbolicType type = monic1.type();
		PrimitivePower[] set1 = monic1.monicFactors(this),
				set2 = monic2.monicFactors(this),
				common = monicFactory.emptySet();
		PrimitivePower[] newSet1 = set1, newSet2 = set2;

		for (PrimitivePower ppower1 : set1) {
			Primitive base = ppower1.primitive(this);
			PrimitivePower ppower2 = monicFactory.get(set2, base);

			if (ppower2 != null) {
				IntObject exponent1 = ppower1.primitivePowerExponent(this);
				IntObject exponent2 = ppower2.primitivePowerExponent(this);
				IntObject minExponent = exponent1.minWith(exponent2);
				IntObject newExponent1 = exponent1.minus(minExponent);
				IntObject newExponent2 = exponent2.minus(minExponent);

				common = monicFactory.put(common,
						primitivePower(base, minExponent));
				if (newExponent1.isPositive())
					newSet1 = monicFactory.put(newSet1,
							primitivePower(base, newExponent1));
				else
					newSet1 = monicFactory.removeKey(newSet1, base);
				if (newExponent2.isPositive())
					newSet2 = monicFactory.put(newSet2,
							primitivePower(base, newExponent2));
				else
					newSet2 = monicFactory.removeKey(newSet2, base);
			}
		}
		return new Monic[] { monic(type, common), monic(type, newSet1),
				monic(type, newSet2) };
	}

	/**
	 * Extracts a common divisor from a nonempty sequence of {@link Monic}s and
	 * modifies the array of monics by replacing each entry with the quotient of
	 * the original entry with the common divisor.
	 * 
	 * @param monics
	 *            non-empty array of {@link Monic}s which all have the same type
	 * @return the common divisor
	 * 
	 * @see {@link #extractCommonality(Monic, Monic)}
	 */
	private Monic extractCommonality(Monic[] monics) {
		int length = monics.length;
		SymbolicType type = monics[0].type();
		PrimitivePower[][] factorSets = new PrimitivePower[length][];
		PrimitivePower[] common = monicFactory.emptySet();

		for (int i = 0; i < length; i++)
			factorSets[i] = monics[i].monicFactors(this);
		for (PrimitivePower pp0 : factorSets[0]) {
			Primitive primitive = pp0.primitive(this);
			int min = pp0.primitivePowerExponent(this).getInt();

			assert min >= 1;
			for (int i = 1; i < length; i++) {
				PrimitivePower pp1 = monicFactory.get(factorSets[i], primitive);

				if (pp1 == null) { // same as exponent 0
					min = 0;
					break;
				}

				int exponent = pp1.primitivePowerExponent(this).getInt();

				if (exponent < min)
					min = exponent;
			}
			if (min == 0)
				continue;
			common = monicFactory.put(common,
					primitivePower(primitive, objectFactory.intObject(min)));
			for (int i = 0; i < length; i++) {
				PrimitivePower[] set = factorSets[i];
				PrimitivePower pp1 = monicFactory.get(set, primitive);
				int exponent = pp1.primitivePowerExponent(this).getInt();
				int newExponent = exponent - min;

				if (newExponent == 0)
					factorSets[i] = monicFactory.removeKey(set, primitive);
				else
					factorSets[i] = monicFactory.put(set, primitivePower(
							primitive, objectFactory.intObject(newExponent)));
			}
			for (int i = 0; i < length; i++)
				monics[i] = monic(type, factorSets[i]);
		}
		return monic(type, common);
	}

	// Monomials...

	/**
	 * Constructs an instance of {@link NTMonomial}, a non-trivial monomial.
	 * 
	 * @param constant
	 *            a {@link Constant} which is neither 0 nor 1
	 * @param monic
	 *            a non-empty {@link Monic} (i.e., not 1)
	 * @return new instance of {@link NTMonomial} as specified
	 */
	private NTMonomial ntMonomial(Constant constant, Monic monic) {
		return new NTMonomial(constant, monic);
	}

	/**
	 * Divides the monomial by the non-zero constant. The monomial and constant
	 * must have the same type. If type is integer, integer division is
	 * performed on the coefficient.
	 * 
	 * @param monomial
	 *            a monomial
	 * @param constant
	 *            a non-zero constant
	 * @return the quotient monomial/constant
	 */
	private Monomial divideMonomialConstant(Monomial monomial,
			Constant constant) {
		return monomial(
				divideConstants(monomial.monomialConstant(this), constant),
				monomial.monic(this));
	}

	/**
	 * Given two {@link Monomial}s <code>m1</code> and <code>m2</code>, this
	 * returns an array of length 3 containing 3 {@link Monomial}s a, g1, g2 (in
	 * that order), satisfying m1=a*g1, m2=a*g2, g1 and g2 have no factors in
	 * common, and a is a {@link Monic}.
	 * 
	 * @param m1
	 *            a non-<code>null</code> {@link Monomial}
	 * @param m2
	 *            a non-<code>null</code> {@link Monomial} of the same type as
	 *            <code>m1</code>
	 * @return the array {a,g1,g2}
	 */
	private Monomial[] extractCommonality(Monomial m1, Monomial m2) {
		Monic[] monicTriple = extractCommonality(m1.monic(this),
				m2.monic(this));

		return new Monomial[] { monicTriple[0],
				monomial(m1.monomialConstant(this), monicTriple[1]),
				monomial(m2.monomialConstant(this), monicTriple[2]) };
	}

	/**
	 * Given two non-zero {@link Monomial}s m1 and m2 of integer type, factor
	 * out common factors, including a positive constant. Returns a triple
	 * (r,q1,q2) of {@link Monomial}s such that:
	 * 
	 * <ul>
	 * <li>m1=r*q1 and m2=r*q2</li>
	 * <li>the GCD of the absolute values of all the coefficients in q1 and q2
	 * together is 1</li>
	 * <li>the factorizations of q1 and q2 have no common factors</li>
	 * <li>the leading coefficient of r is positive</li>
	 * </ul>
	 * 
	 * This is used in integer division and modulus operations. For integer
	 * division: m1/m2 = q1/q2. For modulus: m1%m2 = r*(q1%q2).
	 * 
	 * @param m1
	 *            a non-0 {@link Monomial} of integer type
	 * @param m2
	 *            a non-0 {@link Monomial} of integer type
	 * @return the triple (r,q1,q2) described above
	 */
	private Monomial[] intFactor(Monomial m1, Monomial m2) {
		Monomial[] triple = extractCommonality(m1, m2);
		Monomial r, q1, q2;
		IntegerNumber c1, c2;

		if (triple[0].isOne()) {
			q1 = m1;
			q2 = m2;
			r = oneInt;
		} else {
			q1 = triple[1];
			q2 = triple[2];
			r = triple[0];
		}
		c1 = (IntegerNumber) numberFactory
				.abs(m1.monomialConstant(this).number());
		c2 = (IntegerNumber) numberFactory
				.abs(m2.monomialConstant(this).number());
		if (!c1.isOne() && !c2.isOne()) {
			IntegerNumber gcd = numberFactory.gcd(c1, c2);

			if (!gcd.isOne()) {
				Constant gcdConstant = constant(gcd);

				q1 = divideMonomialConstant(q1, gcdConstant);
				q2 = divideMonomialConstant(q2, gcdConstant);
				r = multiplyConstantMonomial(gcdConstant, r);
			}
		}
		return new Monomial[] { r, q1, q2 };
	}

	/**
	 * <p>
	 * Divides two {@link Monomial}s of integer type. This will always return a
	 * {@link Monomial}, never a non-monomial {@link RationalExpression}. In the
	 * worst case (if the denominator does not evenly divide the numerator), the
	 * result will be a primitive expression ({@link NumericPrimitive}) in which
	 * the operator is {@link SymbolicOperator#INT_DIVIDE}.
	 * </p>
	 * 
	 * <p>
	 * Note on integer division: assume all terms positive. (ad)/(bd) = a/b
	 * </p>
	 * 
	 * @param numerator
	 *            polynomial of integer type
	 * @param denominator
	 *            polynomial of integer type
	 * @return result of division as {@link Monomial}, which might be a new
	 *         primitive expression
	 */
	private Monomial divideIntegerMonomials(Monomial numerator,
			Monomial denominator) {
		assert numerator.type().isInteger();
		assert denominator.type().isInteger();
		if (numerator.isZero())
			return numerator;
		if (denominator.isOne())
			return numerator;
		if (numerator instanceof Constant && denominator instanceof Constant)
			return intDivideConstants((Constant) numerator,
					(Constant) denominator);
		else {
			Monomial[] triple = intFactor(numerator, denominator);

			numerator = triple[1];
			denominator = triple[2];
			if (denominator.isOne())
				return numerator;
			if (numerator instanceof Constant
					&& denominator instanceof Constant)
				return intDivideConstants((Constant) numerator,
						(Constant) denominator);
			return expression(SymbolicOperator.INT_DIVIDE, integerType,
					numerator, denominator);
		}
	}

	/**
	 * <p>
	 * Computes the integer modulus of two {@link Monomial}s of integer type.
	 * </p>
	 * 
	 * <p>
	 * Precondition: this method assumes the numerator is nonnegative and
	 * denominator is positive. The behavior is undefined otherwise.
	 * </p>
	 * 
	 * <p>
	 * Implementation note: The following identity is used:
	 * 
	 * <pre>
	 * (ad)%(bd) = (a%b)d
	 * </pre>
	 * 
	 * Example : (2u)%2 = (u%1)2 = 0.
	 * </p>
	 * 
	 * @param numerator
	 *            an integer monomial assumed to be nonnegative
	 * @param denominator
	 *            an integer monomial assumed to be positive
	 * @return the monomial representing numerator%denominator
	 */
	private Monomial intModulusMonomials(Monomial numerator,
			Monomial denominator) {
		if (numerator.isZero())
			return numerator;
		if (denominator.isOne())
			return zeroInt;
		if (numerator instanceof Constant && denominator instanceof Constant)
			return intModuloConstants((Constant) numerator,
					(Constant) denominator);
		else {
			Monomial[] triple = intFactor(numerator, denominator);

			numerator = triple[1];
			denominator = triple[2];
			if (denominator.isOne())
				return zeroInt;
			if (numerator instanceof Constant
					&& denominator instanceof Constant)
				return multiplyConstantMonomial(
						intModuloConstants((Constant) numerator,
								(Constant) denominator),
						triple[0]);
			else
				return multiplyMonomials(triple[0],
						expression(SymbolicOperator.MODULO, integerType,
								numerator, denominator));
		}
	}

	/**
	 * Divides two {@link Monomial}s of real type. Result is a
	 * {@link RationalExpression}. Simplifications are performed by canceling
	 * common factors as possible.
	 * 
	 * @param numerator
	 *            a non-<code>null</code> monomial of real type
	 * @param denominator
	 *            a non-<code>null</code> non-0 monomial of real type
	 * @return numerator/denominator
	 */
	private RationalExpression divideRealMonomials(Monomial numerator,
			Monomial denominator) {
		assert numerator.type().isReal();
		assert denominator.type().isReal();
		if (numerator.isZero())
			return numerator;
		if (denominator.isOne())
			return numerator;
		else { // cancel common factors...
			Monomial[] triple = extractCommonality(numerator, denominator);

			if (!triple[0].isOne()) {
				numerator = triple[1];
				denominator = triple[2];
			}

			Constant denomConstant = denominator.monomialConstant(this);

			if (!denomConstant.isOne()) {
				denominator = divideMonomialConstant(denominator,
						denomConstant);
				numerator = divideMonomialConstant(numerator, denomConstant);
			}
			if (denominator.isOne())
				return numerator;
			return ntRationalExpression(numerator, denominator);
		}
	}

	/**
	 * Given a {@link Monomial} <i>m</i>, returns an expression equivalent to
	 * <i>m</i>&gt;0. Basic simplifications are performed, e.g., if
	 * <code>polynomial</code> is concrete, a concrete boolean expression is
	 * returned.
	 * 
	 * @param monomial
	 *            a non-<code>null</code> {@link Monomial}
	 * @return an expression equivalent to <code>monomial&gt;0</code>
	 */
	private BooleanExpression isPositive(Monomial monomial) {
		Number number = extractNumber(monomial);

		if (number != null)
			return number.signum() > 0 ? trueExpr : falseExpr;

		SymbolicType type = monomial.type();
		Constant zero = zero(type);
		Monic monic = monomial.monic(this);
		int signum = monomial.monomialConstant(this).number().signum();
		PrimitivePower[] factors = monic.monicFactors(this);
		List<Primitive> positives = new LinkedList<>(),
				nonzeros = new LinkedList<>();

		for (PrimitivePower primitivePower : factors) {
			Primitive primitive = primitivePower.primitive(this);
			int exponent = primitivePower.primitivePowerExponent(this).getInt();

			if (exponent % 2 == 0)
				nonzeros.add(primitive);
			else
				positives.add(primitive);
		}

		BooleanExpression result;
		int numPositives = positives.size();

		if (numPositives == 0) {
			if (signum < 0)
				return falseExpr;
			result = trueExpr;
		} else {
			PrimitivePower[] reducedEntries = positives
					.toArray(new PrimitivePower[numPositives]);
			Monic reducedMonic = monic(type, reducedEntries);

			if (type.isInteger()) {
				// 0<reducedMonic <=> 0<=reducedMonic-1
				// reducedMonic<0 <=> reducedMonic+1<=0
				result = signum > 0
						? isNonnegative(addNoCommon(reducedMonic, negOneInt))
						: isNonpositive(addNoCommon(reducedMonic, oneInt));
			} else {
				result = signum > 0
						? booleanFactory.booleanExpression(
								SymbolicOperator.LESS_THAN, zero, reducedMonic)
						: booleanFactory.booleanExpression(
								SymbolicOperator.LESS_THAN, reducedMonic, zero);
			}
		}
		for (Primitive p : nonzeros) {
			result = booleanFactory.and(result, booleanFactory
					.booleanExpression(SymbolicOperator.NEQ, zero, p));
		}
		return result;
	}

	/**
	 * Given a <code>monomial</code>, returns an expression equivalent to
	 * <code>monomial&lt;0</code>. Basic simplifications are performed, e.g., if
	 * <code>monomial</code> is concrete, a concrete boolean expression is
	 * returned.
	 * 
	 * @param monomial
	 *            a non-<code>null</code> {@link Monomial}
	 * @return an expression equivalent to <code>polynomial&lt;0</code>
	 */
	private BooleanExpression isNegative(Monomial monomial) {
		return isPositive(negate(monomial));
	}

	/**
	 * Given a <code>monomial</code>, returns an expression equivalent to
	 * <code>monomial&ge;0</code> (if <code>geq</code> is <code>true</code>) or
	 * <code>monomial&le;0</code> (if <code>geq</code> is <code>false</code>).
	 * 
	 * Basic simplifications are performed, e.g., if <code>monomial</code> is
	 * concrete, a concrete boolean expression is returned.
	 * 
	 * @param monomial
	 *            a non-<code>null</code> {@link Monomial}
	 * @return an expression equivalent to <<code>monomial&ge;0</code> or
	 *         <code>monomial&le;0</code>
	 */
	private BooleanExpression isLEQ0orGEQ0(Monomial monomial, boolean geq) {
		// X1^2n * X2^2n * Y1^(2n+1) * Y2^(2n+1) >= 0 IFF
		// X1=0 || X2=0 || Y1*Y2>=0
		Number number = extractNumber(monomial);

		if (number != null) {
			if (geq)
				return number.signum() >= 0 ? trueExpr : falseExpr;
			else
				return number.signum() <= 0 ? trueExpr : falseExpr;
		}

		SymbolicType type = monomial.type();
		Constant zero = zero(type);
		Monic monic = monomial.monic(this);
		int signum = monomial.monomialConstant(this).number().signum();
		PrimitivePower[] factors = monic.monicFactors(this);
		List<Primitive> evens = new LinkedList<>(), odds = new LinkedList<>();
		boolean direction = geq ? signum > 0 : signum < 0;
		// direction true means the monic should be >=0: 3x^2>=0 or -3x^2<=0.
		// direction false means the monic should be <=0: 3x^2<=0 or -3x^2>=0

		assert signum != 0;
		for (PrimitivePower primitivePower : factors) {
			Primitive p = primitivePower.primitive(this);
			int exponent = primitivePower.primitivePowerExponent(this).getInt();

			if (exponent % 2 != 0)
				odds.add(p);
			else
				evens.add(p);
		}

		int numOdds = odds.size();

		if (numOdds == 0 && direction)
			return trueExpr;

		BooleanExpression result = falseExpr;

		for (Primitive p : evens)
			result = booleanFactory.or(result, booleanFactory
					.booleanExpression(SymbolicOperator.EQUALS, zero, p));
		if (numOdds > 0) {
			PrimitivePower[] reducedEntries = odds
					.toArray(new PrimitivePower[numOdds]);
			Monic reducedMonic = monic(type, reducedEntries);

			result = booleanFactory.or(result,
					direction
							? booleanFactory.booleanExpression(
									SymbolicOperator.LESS_THAN_EQUALS, zero,
									reducedMonic)
							: booleanFactory.booleanExpression(
									SymbolicOperator.LESS_THAN_EQUALS,
									reducedMonic, zero));
		}
		return result;
	}

	/**
	 * Given a <code>monomial</code>, returns an expression equivalent to
	 * <code>0&le;monomial</code>. Basic simplifications are performed, e.g., if
	 * <code>monomial</code> is concrete, a concrete boolean expression is
	 * returned.
	 * 
	 * @param monomial
	 *            a non-<code>null</code> {@link Monomial}
	 * @return an expression equivalent to <code>0&le;monomial</code>
	 */
	private BooleanExpression isNonnegative(Monomial monomial) {
		return isLEQ0orGEQ0(monomial, true);
	}

	/**
	 * Computes an expression equivalent to <code>monomial</code> &le; 0.
	 * 
	 * @param monomial
	 *            any non-<code>null</code> {@link Monomial}
	 * @return an expression equivalent to <code>monomial</code> &le; 0
	 */
	private BooleanExpression isNonpositive(Monomial monomial) {
		return isLEQ0orGEQ0(monomial, false);
	}

	/**
	 * Computes an expression equivalent to "monomial != 0".
	 * 
	 * @param monomial
	 *            any non-<code>null</code> {@link Monomial}
	 * @return an expression equivalent to <code>monomial</code> != 0
	 */
	private BooleanExpression isNonZero(Monomial monomial) {
		// X1^n1...Xn^nr !=0 iff X1!=0 && ... && Xn!=0
		Number number = extractNumber(monomial);

		if (number != null)
			return number.isZero() ? falseExpr : trueExpr;

		SymbolicType type = monomial.type();
		Constant zero = zero(type);
		Monic monic = monomial.monic(this);
		BooleanExpression result = trueExpr;

		for (Primitive p : monicFactory.getKeys(monic.monicFactors(this))) {
			// consider expanding p
			result = booleanFactory.and(result, booleanFactory
					.booleanExpression(SymbolicOperator.NEQ, zero, p));
		}
		return result;
	}

	/**
	 * Given two monomials <code>p1</code> and <code>p2</code>, returns an
	 * expression equivalent to <code>p1&gt;0 && p2&gt;0</code>.
	 * 
	 * @param p1
	 *            a non-<code>null</code> {@link Monomial}
	 * @param p2
	 *            a non-<code>null</code> {@link Monomial} of same type as
	 *            <code>p1</code>
	 * @return an expression equivalent to <code>p1&gt;0 && p2&gt;0</code>
	 */
	private BooleanExpression arePositive(Monomial p1, Monomial p2) {
		BooleanExpression result = isPositive(p1);

		if (result.isFalse())
			return result;
		return booleanFactory.and(result, isPositive(p2));
	}

	/**
	 * Given two polynomials <code>p1</code> and <code>p2</code>, returns an
	 * expression equivalent to <code>p1&lt;0 && p2&lt;0</code>.
	 * 
	 * @param p1
	 *            a non-<code>null</code> {@link Monomial}
	 * @param p2
	 *            a non-<code>null</code> {@link Monomial} of same type as
	 *            <code>p1</code>
	 * @return an expression equivalent to <code>p1&lt;0 && p2&lt;0</code>
	 */
	private BooleanExpression areNegative(Monomial p1, Monomial p2) {
		BooleanExpression result = isNegative(p1);

		if (result.isFalse())
			return result;
		return booleanFactory.and(result, isNegative(p2));
	}

	private Monomial addNoCommon(Monomial m1, Monomial m2) {
		Monomial[] t1 = m1.termMap(this), t2 = m2.termMap(this),
				t = addTermMaps(t1, t2);

		if (t.length == 0)
			return zero(m1.type());
		else
			return factorTermMap(t);
	}

	// Term maps...

	/**
	 * <p>
	 * Computes the constant that should be factored out of every term in a term
	 * map in order to produce a polynomial in normal form. For integer type,
	 * this is the GCD (greatest common divisor) of the absolute values of the
	 * coefficients, multiplied by the sign of the leading coefficient. For real
	 * type, it is just the coefficient of the leading term.
	 * </p>
	 * 
	 * <p>
	 * Note that in any case, after dividing every term by the constant factor,
	 * the leading term will have a positive coefficient. For real type, the
	 * leading coefficient will be 1. For integer type, the GCD of the absolute
	 * values of the coefficients will be 1.
	 * </p>
	 * 
	 * <p>
	 * Precondition: <code>termMap</code> is non-empty
	 * </p>
	 * 
	 * @param terms
	 *            a term map: a map from {@link Monic} to {@link Monomial} with
	 *            the property that a {@link Monic} <i>m</i> maps to a
	 *            {@link Monomial} of the form <i>c</i>*<i>m</i>, for some non-0
	 *            {@link Constant} <i>c</i>
	 * @return the constant that should be factored out of the entire term map
	 *         in order to bring the term map into a normal form
	 */
	private Constant getConstantFactor(Monomial[] terms) {
		int n = terms.length;
		Monomial leadingMonomial = terms[0];
		SymbolicType type = leadingMonomial.type();
		Constant leadingConstant = leadingMonomial.monomialConstant(this);

		if (type.isInteger()) {
			Number leadingNumber = leadingConstant.number();
			IntegerNumber gcd = (IntegerNumber) numberFactory
					.abs(leadingNumber);

			for (int i = 1; i < n; i++) {
				IntegerNumber coefficient = (IntegerNumber) terms[i]
						.monomialConstant(this).number();

				gcd = numberFactory.gcd(gcd,
						(IntegerNumber) numberFactory.abs(coefficient));
				if (gcd.isOne())
					break;
			}
			return constant(leadingNumber.signum() < 0
					? numberFactory.negate(gcd) : gcd);
		} else {
			return leadingConstant;
		}
	}

	/**
	 * Multiplies a monomial with every element in a term map, producing a new
	 * term map. If the given term map is sorted using the
	 * {@link #monicComparator}, so will the new one be.
	 * 
	 * @param monomial
	 *            a non-zero monomial
	 * @param terms
	 *            a term map: map from Monic to Monomial such that each monic m
	 *            is mapped to a non-zero constant times m
	 * @return the term map obtained by multiplying the monic by every element
	 *         of the given term map
	 */
	private Monomial[] multiplyMonomialTermMap(Monomial monomial,
			Monomial[] terms) {
		Number number = monomial.monomialConstant(this).number();
		Monic monic = monomial.monic(this);
		int n = terms.length;
		Monomial[] newTerms = new Monomial[n];

		for (int i = 0; i < n; i++) {
			Monomial term = terms[i];
			Number newNumber = numberFactory.multiply(number,
					term.monomialConstant(this).number());
			Monic newMonic = multiplyMonics(monic, term.monic(this));

			newTerms[i] = monomial(constant(newNumber), newMonic);
		}
		return newTerms;
	}

	/**
	 * Multiplies two term maps using methods
	 * {@link #multiplyMonomialTermMap(Monomial, SymbolicMap)} and
	 * {@link #add(SymbolicMap, SymbolicMap)}.
	 * 
	 * @param terms1
	 *            a non-empty term map
	 * @param terms2
	 *            a non-empty term map of same type
	 * @return result of multiplying the two term maps
	 */
	private Monomial[] multiplyTermMaps2(Monomial[] terms1, Monomial[] terms2) {
		Monomial[] result = polynomialFactory.emptySet();

		for (Monomial monomial1 : terms1) {
			Monomial[] product = multiplyMonomialTermMap(monomial1, terms2);

			result = addTermMaps(result, product);
		}
		return result;
	}

	// Rational expressions...

	/**
	 * <p>
	 * Adds two rational expressions. The factorizations are used so that in the
	 * resulting rational expression, the numerator and denominator have not
	 * common factors.
	 * </p>
	 * 
	 * <p>
	 * Note: result = a1/b1 + a2/b2 = (a1*b2 + a2*b1)/(b1*b2). Let d=gcd(b1,b2).
	 * Then result = (a1*(b2/d)+a2*(b1/d))/(b1*b2/d)
	 * </p>
	 * 
	 * @param r1
	 *            a non-<code>null</code> rational expression
	 * @param r2
	 *            a non-<code>null</code> rational expression of the same type
	 *            as <code>r1</code>
	 * @return the sum r1+r2
	 */
	private RationalExpression addRational(RationalExpression r1,
			RationalExpression r2) {
		Monomial a1 = r1.numerator(this), a2 = r2.numerator(this);
		Monomial b1 = r1.denominator(this), b2 = r2.denominator(this);
		Monomial[] triple = extractCommonality(b1, b2);
		Monomial b1divgcd = triple[1], b2divgcd = triple[2];
		Monomial numerator = addMonomials(multiplyMonomials(a1, b2divgcd),
				multiplyMonomials(a2, b1divgcd));
		Monomial denominator = multiplyMonomials(b1, b2divgcd);

		return divideRealMonomials(numerator, denominator);
	}

	private BooleanExpression isZero(RationalExpression rational) {
		return isZero(rational.numerator(this));
	}

	private BooleanExpression isNonZero(RationalExpression rational) {
		return isNonZero(rational.numerator(this));
	}

	/**
	 * Multiplies two rational expressions.
	 * 
	 * @param r1
	 *            a non-<code>null</code> {@link RationalExpression}
	 * @param r2
	 *            a non-<code>null</code> {@link RationalExpression} of the same
	 *            type as <code>r1</code>
	 * @return the product of <code>r1</code> and <code>r2</code>
	 */
	private RationalExpression multiplyRational(RationalExpression r1,
			RationalExpression r2) {
		// (n1/d1)*(n2/d2)
		if (r1.isZero())
			return r1;
		if (r2.isZero())
			return r2;
		if (r1.isOne())
			return r2;
		if (r2.isOne())
			return r1;

		// performance debug:
		// r1 = objectFactory.canonic(r1);
		// r2 = objectFactory.canonic(r2);

		return divideRealMonomials(
				multiplyMonomials(r1.numerator(this), r2.numerator(this)),
				multiplyMonomials(r1.denominator(this), r2.denominator(this)));
	}

	/**
	 * Returns 1/r, where r is a rational expression (which must necessarily
	 * have real type).
	 * 
	 * @param r
	 *            a rational expression
	 * @return 1/r
	 */
	private RationalExpression invert(RationalExpression r) {
		return divideRealMonomials(r.denominator(this), r.numerator(this));
	}

	/**
	 * Division of two rational expressions of real type.
	 * 
	 * Precondition: type is real.
	 * 
	 * @param r1
	 *            a rational expression of real type
	 * @param r2
	 *            a rational expression of real type
	 * @return r1/r2 as rational expression
	 */
	private RationalExpression divideRationals(RationalExpression r1,
			RationalExpression r2) {
		assert r1.type().isReal();
		return multiplyRational(r1, invert(r2));
	}

	/**
	 * Negates a rational expression, i.e., given a rational expression p/q,
	 * returns the rational expression -p/q.
	 * 
	 * @param rational
	 *            a non-<code>null</code> {@link RationalExpression}
	 * @return negation of that rational expression in normal form
	 */
	private RationalExpression negate(RationalExpression rational) {
		return divideRealMonomials(negate(rational.numerator(this)),
				rational.denominator(this));
	}

	// General numeric expressions...

	/**
	 * Computes the sum of the results of casting the elements in a symbolic
	 * collection to real..
	 * 
	 * @param args
	 *            a non-<code>null</code> {@link SymbolicCollection} in which
	 *            every element is an instance of
	 * @return an expression equivalent to the result of summing the casts to
	 *         real of the elements of the collection
	 */
	private NumericExpression addWithCast(Monomial[] args) {
		int n = args.length;
		Monomial[] castArgs = new Monomial[n];
		boolean unreal = false;

		for (int i = 0; i < n; i++) {
			Monomial arg = args[i];

			unreal = unreal || !arg.type().isReal();
			castArgs[i] = (Monomial) castToReal(arg);
		}
		return addMonomials(unreal ? castArgs : args);
	}

	/**
	 * Computes the product of the results of casting the elements in a symbolic
	 * collection to real. The elements of the collection must all be instances
	 * of {@link IdealExpression}.
	 * 
	 * @param args
	 *            a non-<code>null</code> {@link SymbolicCollection} in which
	 *            every element is an instance of {@link IdealExpression}
	 * @return an expression equivalent to the result of multiplying the casts
	 *         to real of the elements of the collection
	 */
	private Monomial multiplyWithCast(Monomial[] args) {
		int n = args.length;
		Monomial result = null;

		if (n == 0)
			throw new IllegalArgumentException(
					"Collection must contain at least one element");
		for (Monomial arg : args) {
			if (result == null)
				result = (Monomial) castToReal(arg);
			else
				result = multiplyMonomials(result, (Monomial) castToReal(arg));
		}
		return result;
	}

	/**
	 * Computes result of raising <code>base</code> to the <code>exponent</code>
	 * power.
	 * 
	 * @param base
	 *            a non-<code>null</code> {@link IdealExpression}
	 * 
	 * @param exponent
	 *            the exponent, which must be positive
	 * @return the result of raising base to the power exponent
	 */
	private RationalExpression powerNumericInteger(NumericExpression base,
			IntegerNumber exponent) {
		// nothing can be done if exponent is larger than max int because
		// the canonical form uses Java ints for exponents...
		return ((RationalExpression) base).powerInt(this, exponent.intValue());
	}

	/**
	 * <p>
	 * Computes power when exponent is not concrete or not integral.
	 * </p>
	 * 
	 * <p>
	 * Preconditions: <code>exponent</code> is not a concrete integer.
	 * <code>base</code> is not 0 or 1.
	 * </p>
	 *
	 * @param base
	 *            the base is the power operation
	 * @param exponent
	 *            the exponent in the power operation
	 * @return expression equivalent to raising <code>base</code> to the
	 *         <code>exponent</code> power
	 */
	private RationalExpression powerGeneral(RationalExpression base,
			RationalExpression exponent) {
		IntegerNumber c1 = getConcreteExponent(exponent);

		if (c1.isOne())
			return base.powerRational(this, exponent);

		// now c1 is not 1. It might be -1.

		RationalExpression newExponent = divide(exponent,
				constant(exponent.type().isInteger() ? c1
						: numberFactory.integerToRational(c1)));
		RationalExpression result = base.powerRational(this, newExponent);
		boolean invert;

		if (c1.signum() < 0) {
			c1 = numberFactory.negate(c1);
			invert = true;
		} else {
			invert = false;
		}

		// now c1 is a positive integer, maybe 1

		if (!c1.isOne())
			result = powerNumericInteger(result, c1);
		if (invert)
			result = invert(result);
		return result;
	}

	/**
	 * <p>
	 * Computes the result of casting any {@link IdealExpression} to real type.
	 * If <code>numericExpression</code> already has real type, it is returned
	 * as is. Otherwise, it has integer type, and the result depends on the
	 * operator of the expression.
	 * </p>
	 * 
	 * <p>
	 * For ideal arithmetic, casting commutes with most operations, i.e., cast(a
	 * O p) = cast(a) O cast(p), for O=+,-,*. However, not integer division. Not
	 * integer modulus. Primitives get a {@link SymbolicOperator#CAST} in front
	 * of them. {@link Constant}s get cast by the {@link #numberFactory}.
	 * </p>
	 * 
	 * @param numericExpression
	 *            a non-<code>null</code> {@link IdealExpression}
	 */
	private NumericExpression castToReal(NumericExpression numericExpression) {
		if (numericExpression.type().isReal())
			return numericExpression;

		SymbolicOperator operator = numericExpression.operator();

		switch (operator) {
		case ADD:
			return addWithCast(((Polynomial) numericExpression).termMap(this));
		case CONCRETE:
			return constant(numberFactory
					.rational(((NumberObject) numericExpression.argument(0))
							.getNumber()));
		case COND:
			return expression(operator, realType, numericExpression.argument(0),
					castToReal(
							(NumericPrimitive) numericExpression.argument(1)),
					castToReal(
							(NumericPrimitive) numericExpression.argument(2)));
		case MULTIPLY: {
			Monomial monomial = (Monomial) numericExpression;
			Constant constant = monomial.monomialConstant(this);
			Monic monic = monomial.monic(this);
			Monomial result = (Monomial) castToReal(constant);

			result = multiplyMonomials(result,
					multiplyWithCast(monic.monicFactors(this)));
			return result;
		}
		case NEGATIVE:
			return minus(castToReal(
					(NumericExpression) numericExpression.argument(0)));
		case POWER: {
			NumericExpression realBase = castToReal(
					(NumericExpression) numericExpression.argument(0));
			SymbolicObject arg1 = numericExpression.argument(1);

			if (arg1.symbolicObjectKind() == SymbolicObjectKind.INT)
				return power(realBase, (IntObject) arg1);
			else
				return power(realBase, castToReal((NumericExpression) arg1));
		}
		case SUBTRACT:
			return subtract(
					castToReal(
							(NumericExpression) numericExpression.argument(0)),
					castToReal(
							(NumericExpression) numericExpression.argument(1)));
		// Primitives...
		case APPLY:
		case ARRAY_READ:
		case CAST:
		case INT_DIVIDE:
		case LENGTH:
		case MODULO:
		case SYMBOLIC_CONSTANT:
		case TUPLE_READ:
		case UNION_EXTRACT:
			return expression(SymbolicOperator.CAST, realType,
					numericExpression);
		default:
			throw new SARLInternalException("Should be unreachable");
		}
	}

	/**
	 * Given two numeric expressions <code>arg0</code> and <code>arg1</code>,
	 * returns a boolean expression equivalent to <code>arg0&le;arg1</code>. The
	 * result will be in ideal form, i.e., <code>0&le;arg1-arg0</code>.
	 * Implementation uses {@link #isNonnegative(Monomial)} and
	 * {@link #isNonnegative(RationalExpression)}.
	 * 
	 * @param arg0
	 *            a non-<code>null</code> {@link IdealExpression}
	 * @param arg1
	 *            a non-<code>null</code> {@link IdealExpression} of the same
	 *            type as <code>arg0</code>
	 * @return an expression equivalent to <code>0&le;arg1-arg0</code>
	 */
	private BooleanExpression lessThanEqualsMain(NumericExpression arg0,
			NumericExpression arg1) {
		NumericExpression difference = subtract(arg1, arg0);

		return difference instanceof Monomial
				? isNonnegative((Monomial) difference)
				: isNonnegative((RationalExpression) difference);
	}

	// ***************** Package-private methods **********************

	/**
	 * Returns the sum of two constants. The two constants must have the same
	 * type (both integer, or both real).
	 * 
	 * @param c1
	 *            any non-<code>null</code> {@link Constant}
	 * @param c2
	 *            a non-<code>null</code> {@link Constant} of same type as
	 *            <code>c1</code>
	 * @return the sum of the two constants
	 */
	 Constant add(Constant c1, Constant c2) {
		return constant(objectFactory
				.numberObject(numberFactory.add(c1.number(), c2.number())));
	}

	/**
	 * Computes the negation of a monomial (i.e., multiplication by -1).
	 * 
	 * @param monomial
	 *            any non-<code>null</code> {@link Monomial}
	 * @return the monomial which is the negation of the given one
	 */
	private Monomial negate(Monomial monomial) {
		return monomial(negate(monomial.monomialConstant(this)),
				monomial.monic(this));
	}

	// ********** Methods specified in NumericExpressionFactory ***********

	@Override
	public void init() {
	}

	@Override
	public NumberFactory numberFactory() {
		return numberFactory;
	}

	@Override
	public BooleanExpressionFactory booleanFactory() {
		return booleanFactory;
	}

	@Override
	public ObjectFactory objectFactory() {
		return objectFactory;
	}

	@Override
	public One oneInt() {
		return oneInt;
	}

	@Override
	public One oneReal() {
		return oneReal;
	}

	@Override
	public NumericPrimitive expression(SymbolicOperator operator,
			SymbolicType numericType, SymbolicObject... arguments) {
		return new NumericPrimitive(operator, numericType, arguments);
	}

	@Override
	public BooleanExpression isZero(Monomial monomial) {
		// X1^n1...Xn^nr =0 iff X1=0 || ... || Xn=0
		Number number = extractNumber(monomial);

		if (number != null)
			return number.isZero() ? trueExpr : falseExpr;

		SymbolicType type = monomial.type();
		Constant zero = zero(type);
		Monic monic = monomial.monic(this);
		BooleanExpression result = falseExpr;

		for (Primitive p : monicFactory.getKeys(monic.monicFactors(this))) {
			// consider expanding p
			result = booleanFactory.or(result, booleanFactory
					.booleanExpression(SymbolicOperator.EQUALS, zero, p));
		}
		return result;
	}

	@Override
	public RationalExpression add(NumericExpression arg0,
			NumericExpression arg1) {
		if (arg0 instanceof Constant && arg1 instanceof Constant)
			return add((Constant) arg0, (Constant) arg1);
		if (arg0.type().isInteger())
			return addMonomials((Monomial) arg0, (Monomial) arg1);
		else
			return addRational((RationalExpression) arg0,
					(RationalExpression) arg1);
	}

	@Override
	public RationalExpression subtract(NumericExpression arg0,
			NumericExpression arg1) {
		return add(arg0, minus(arg1));
	}

	@Override
	public RationalExpression multiply(NumericExpression arg0,
			NumericExpression arg1) {
		if (arg0 instanceof Constant && arg1 instanceof Constant)
			return multiplyConstants((Constant) arg0, (Constant) arg1);
		if (arg0.type().isInteger())
			return multiplyMonomials((Monomial) arg0, (Monomial) arg1);
		else
			return multiplyRational((RationalExpression) arg0,
					(RationalExpression) arg1);
	}

	@Override
	public RationalExpression divide(NumericExpression arg0,
			NumericExpression arg1) {
		if (arg0 instanceof Constant && arg1 instanceof Constant)
			return divideConstants((Constant) arg0, (Constant) arg1);
		if (arg0.type().isInteger())
			return divideIntegerMonomials((Monomial) arg0, (Monomial) arg1);
		if (arg0 instanceof Monomial && arg1 instanceof Monomial)
			return divideRealMonomials((Monomial) arg0, (Monomial) arg1);
		return divideRationals((RationalExpression) arg0,
				(RationalExpression) arg1);
	}

	@Override
	public NumericExpression modulo(NumericExpression arg0,
			NumericExpression arg1) {
		return intModulusMonomials((Monomial) arg0, (Monomial) arg1);
	}

	@Override
	public NumericExpression minus(NumericExpression arg) {
		if (arg.isZero())
			return arg;
		if (arg instanceof Constant)
			return negate((Constant) arg);
		if (arg instanceof Monomial)
			return negate((Monomial) arg);
		else
			return negate((RationalExpression) arg);
	}

	@Override
	public NumericExpression power(NumericExpression base, IntObject exponent) {
		int n = exponent.getInt();

		assert n >= 0;
		if (n == 0)
			return one(base.type());
		if (n == 1)
			return base;
		return ((RationalExpression) base).powerInt(this, n);
	}

	@Override
	public IntegerNumber getConcreteExponent(RationalExpression exponent) {
		Monomial num = exponent.numerator(this);
		Number c = num.monomialConstant(this).number();

		if (c instanceof IntegerNumber) {
			return (IntegerNumber) c;
		} else {
			return numberFactory.numerator((RationalNumber) c);
		}
	}

	@Override
	public RationalExpression power(NumericExpression base,
			NumericExpression exponent) {
		Number exponentNumber = extractNumber(exponent);
		boolean isInteger = base.type().isInteger();

		if (exponentNumber != null) {
			if (exponentNumber instanceof RationalNumber) {
				RationalNumber rat = (RationalNumber) exponentNumber;

				if (numberFactory.isIntegral(rat))
					exponentNumber = numberFactory.integerValue(rat);
			}
			if (exponentNumber instanceof IntegerNumber) {
				IntegerNumber exponentInteger = (IntegerNumber) exponentNumber;
				int signum = exponentNumber.signum();

				if (signum > 0)
					return powerNumericInteger(base, exponentInteger);
				else if (signum < 0) {
					if (isInteger)
						throw new SARLException(
								"Power expression with integer base and negative exponent:\n"
										+ base + "\n" + exponent);
					return invert((RationalExpression) powerNumericInteger(base,
							numberFactory.negate(exponentInteger)));
				} else { // exponent = 0
					if (base.isZero())
						throw new SARLException("0^0 is undefined");
					return isInteger ? oneInt : oneReal;
				}
			}
		}

		// at this point exponent is not a concrete integer

		if (base.isZero())
			return isInteger ? zeroInt : zeroReal;
		if (base.isOne())
			return isInteger ? oneInt : oneReal;

		return powerGeneral((RationalExpression) base,
				(RationalExpression) exponent);
	}

	@Override
	public NumericExpression cast(NumericExpression numericExpression,
			SymbolicType newType) {
		if (numericExpression.type().isIdeal() && newType.equals(realType))
			return castToReal(numericExpression);
		if (numericExpression.type().isReal() && newType.equals(integerType)) {
			RationalNumber number = (RationalNumber) extractNumber(
					numericExpression);

			if (number != null) {
				int sign = number.signum();

				if (sign >= 0) {
					return constant(numberFactory.floor(number));
				} else {
					return constant(numberFactory.ceil(number));
				}
			}
		}
		return expression(SymbolicOperator.CAST, newType, numericExpression);
	}

	@Override
	public Number extractNumber(NumericExpression expression) {
		if (expression instanceof Constant)
			return ((Constant) expression).number();
		return null;
	}

	@Override
	public NumericExpression number(NumberObject numberObject) {
		return constant(numberObject);
	}

	@Override
	public NumericSymbolicConstant symbolicConstant(StringObject name,
			SymbolicType type) {
		return new IdealSymbolicConstant(name, type);
	}

	@Override
	public SymbolicTypeFactory typeFactory() {
		return typeFactory;
	}

	@Override
	public IdealComparator comparator() {
		return comparator;
	}

	@Override
	public BooleanExpression lessThan(NumericExpression arg0,
			NumericExpression arg1) {
		Number num0 = extractNumber(arg0);

		if (num0 != null) {
			Number num1 = extractNumber(arg1);

			if (num1 != null) // num0-num1<0 <=> num0<num1
				return numberFactory.compare(num0, num1) < 0 ? this.trueExpr
						: this.falseExpr;
		}

		NumericExpression difference = subtract(arg1, arg0);

		return difference instanceof Monomial
				? isPositive((Monomial) difference)
				: isPositive((RationalExpression) difference);
	}

	@Override
	public BooleanExpression lessThanEquals(NumericExpression arg0,
			NumericExpression arg1) {
		Number num0 = extractNumber(arg0);

		if (num0 != null) {
			Number num1 = extractNumber(arg1);

			if (num1 != null) // num0-num1<=0 <=> num0<=num1
				return numberFactory.compare(num0, num1) <= 0 ? this.trueExpr
						: falseExpr;
		}
		return lessThanEqualsMain(arg0, arg1);
	}

	@Override
	public BooleanExpression notLessThan(NumericExpression arg0,
			NumericExpression arg1) {
		return lessThanEquals(arg1, arg0);
	}

	@Override
	public BooleanExpression notLessThanEquals(NumericExpression arg0,
			NumericExpression arg1) {
		return lessThan(arg1, arg0);
	}

	@Override
	public BooleanExpression equals(NumericExpression arg0,
			NumericExpression arg1) {
		if (arg0.equals(arg1))
			return trueExpr;
		// if they are constants but not equal, return false:
		if (arg0 instanceof Constant && arg1 instanceof Constant)
			return falseExpr;

		NumericExpression difference = subtract(arg1, arg0);

		return isZero((RationalExpression) difference);
	}

	@Override
	public BooleanExpression neq(NumericExpression arg0,
			NumericExpression arg1) {
		if (arg0.equals(arg1))
			return falseExpr;
		if (arg0 instanceof Constant && arg1 instanceof Constant)
			return trueExpr;

		NumericExpression difference = subtract(arg1, arg0);

		return isNonZero((RationalExpression) difference);
	}

	// ***************** Methods specified in IdealFactory ******************

	@Override
	public IntObject oneIntObject() {
		return oneIntObject;
	}

	@Override
	public Constant intConstant(int value) {
		if (value == 1)
			return oneInt;
		return new NTConstant(integerType,
				objectFactory.numberObject(numberFactory.integer(value)));
	}

	@Override
	public Constant constant(Number number) {
		return constant(objectFactory.numberObject(number));
	}

	@Override
	public Constant zeroInt() {
		return zeroInt;
	}

	@Override
	public Constant zeroReal() {
		return zeroReal;
	}

	@Override
	public Constant zero(SymbolicType type) {
		return type.isInteger() ? zeroInt : zeroReal;
	}

	@Override
	public One one(SymbolicType type) {
		return type.isInteger() ? oneInt : oneReal;
	}

	@Override
	public Monic monic(SymbolicType type, PrimitivePower[] factorSet) {
		int n = factorSet.length;

		if (n == 0)
			return one(type);
		if (n == 1)
			return factorSet[0];
		return ntMonic(type, factorSet);
	}

	@Override
	public Monomial monomial(Constant constant, Monic monic) {
		if (constant.isZero())
			return constant;
		if (constant.isOne())
			return monic;
		if (monic.isTrivialMonic())
			return constant;
		// zirkel: A constant times big-O is just big-O
		if (monic.operator() == SymbolicOperator.APPLY
				&& ((SymbolicConstant) monic.argument(0)).name().toString()
						.equals("BIG_O")) {
			return monic;
		}
		return ntMonomial(constant, monic);
	}

	@Override
	public Monomial factorTermMap(Monomial[] terms) {
		int size = terms.length;

		assert size != 0;

		if (size == 1)
			return terms[0];

		Monic[] monics = new Monic[size];

		for (int i = 0; i < size; i++)
			monics[i] = terms[i].monic(this);

		Monic monic = extractCommonality(monics);
		Constant constant = getConstantFactor(terms);
		SymbolicType type = constant.type();
		Monomial[] newTerms = new Monomial[size];

		for (int i = 0; i < size; i++)
			newTerms[i] = monomial(
					divideConstants(terms[i].monomialConstant(this), constant),
					monics[i]);

		Polynomial polynomial = polynomial(type, newTerms);
		Monomial result = monomial(constant, multiplyMonics(monic, polynomial));

		return result;
	}

	@Override
	public Monomial addMonomials(Monomial m1, Monomial m2) {
		assert m1.type().equals(m2.type());
		if (m1.isZero())
			return m2;
		if (m2.isZero())
			return m1;

		Monomial[] triple = extractCommonality(m1, m2);
		// p1+p2=a(q1+q2)

		if (triple[0].isOne())
			return addNoCommon(m1, m2);
		return multiplyMonomials(triple[0], addNoCommon(triple[1], triple[2]));
	}

	// adds arbitrary monomials all of the same type.
	// e.g.: {x,x,2x,x+xy,xy,xz} -> x*(2y+z+5) = 2*x*(y+(1/2)z+(5/2))
	@Override
	public Monomial addMonomials(Monomial[] monomials) {
		int size = monomials.length;
		Monomial[] terms = monomials[0].termMap(this);

		for (int i = 1; i < size; i++)
			terms = addTermMaps(terms, monomials[i].termMap(this));
		return terms.length == 0 ? zero(monomials[0].type())
				: factorTermMap(terms);
	}

	@Override
	public PrimitivePower primitivePower(Primitive primitive,
			IntObject exponent) {
		if (exponent.isZero())
			throw new IllegalArgumentException(
					"Exponent to primitive power must be positive: "
							+ primitive);
		if (exponent.isOne())
			return primitive;
		return ntPrimitivePower(primitive, exponent);
	}

	@Override
	public NTPolynomial polynomial(SymbolicType type, Monomial[] terms) {
		return new NTPolynomial(type, terms);
	}

	@Override
	public Monomial[] addTermMaps(Monomial[] terms1, Monomial[] terms2) {
		return polynomialFactory.combine(monomialAdder, terms1, terms2);
	}

	@Override
	public Monomial[] multiplyConstantTermMap(Constant constant,
			Monomial[] terms) {
		if (constant.isOne())
			return terms;

		int n = terms.length;
		Monomial[] newTerms = new Monomial[n];

		for (int i = 0; i < n; i++) {
			newTerms[i] = multiplyConstantMonomial(constant, terms[i]);
		}
		return newTerms;
	}

	@Override
	public Monomial multiplyMonomials(Monomial m1, Monomial m2) {
		return monomial(
				multiplyConstants(m1.monomialConstant(this),
						m2.monomialConstant(this)),
				multiplyMonics(m1.monic(this), m2.monic(this)));
	}

	@Override
	public Monomial[] multiplyTermMaps(Monomial[] termMap1,
			Monomial[] termMap2) {
		Monomial[] result;
		int n1 = termMap1.length, n2 = termMap2.length;

		if (debug) {
			System.out.println(
					"Debug: multiplying maps of size: " + n1 + ", " + n2);
			System.out.flush();
		}
		if (n1 <= n2)
			result = multiplyTermMaps2(termMap1, termMap2);
		else
			result = multiplyTermMaps2(termMap2, termMap1);
		if (debug) {
			System.out.println(
					"Debug: completed multiplication with result size: "
							+ result.length);
			System.out.flush();
		}
		return result;
	}

	@Override
	public Monomial multiplyConstantMonomial(Constant constant,
			Monomial monomial) {
		return monomial(
				multiplyConstants(constant, monomial.monomialConstant(this)),
				monomial.monic(this));
	}

	@Override
	public Monomial[] oneTermMap(SymbolicType type) {
		if (type.isInteger())
			return oneTermListInt;
		else
			return oneTermListReal;
	}

	@Override
	public BooleanExpression isPositive(RationalExpression rational) {
		Number number = extractNumber(rational);
	
		if (number == null) {
			Monomial numerator = rational.numerator(this);
			Monomial denominator = rational.denominator(this);
			BooleanExpression result = arePositive(numerator, denominator);
	
			if (result.isTrue())
				return result;
			return booleanFactory.or(result,
					areNegative(numerator, denominator));
		}
		return number.signum() > 0 ? trueExpr : falseExpr;
	}

	@Override
	public BooleanExpression isNonnegative(RationalExpression rational) {
		Number number = extractNumber(rational);
	
		if (number == null) {
			Monomial numerator = rational.numerator(this);
			Monomial denominator = rational.denominator(this);
			BooleanExpression result = booleanFactory
					.and(isNonnegative(numerator), isPositive(denominator));
	
			if (result.isTrue())
				return result;
			return booleanFactory.or(result, booleanFactory.and(
					isNonnegative(negate(numerator)), isNegative(denominator)));
		}
		return number.signum() >= 0 ? trueExpr : falseExpr;
	}

	@Override
	public Monomial[] powerTermMap(SymbolicType type, Monomial[] map,
			IntObject exponent) {
		Monomial[] result = oneTermMap(type);
		int n = exponent.getInt();

		assert n >= 0;
		if (n > 0) {
			while (true) {
				if (n % 2 != 0) {
					result = multiplyTermMaps(result, map);
					n -= 1;
					if (n == 0)
						break;
				}
				map = multiplyTermMaps(map, map);
				n /= 2;
			}
		}
		return result;
	}

	@Override
	public Comparator<Monic> monicComparator() {
		return monicComparator;
	}

	@Override
	public Monic monicMask(Monic monic, boolean[] mask) {
		int count = 0;
		int n = mask.length;

		for (int i = 0; i < n; i++)
			if (mask[i])
				count++;

		if (count == n)
			return monic;

		PrimitivePower[] factors = monic.monicFactors(this),
				newFactors = new PrimitivePower[count];
		int j = 0;

		assert n == factors.length;
		for (int i = 0; i < n; i++) {
			if (mask[i]) {
				newFactors[j] = factors[i];
				j++;
			}
		}
		return monic(monic.type(), newFactors);
	}

	// Rational expressions...

	@Override
	public NTRationalExpression ntRationalExpression(Monomial numerator,
			Monomial denominator) {
		return new NTRationalExpression(numerator, denominator);
	}

	@Override
	public KeySetFactory<Monic, Monomial> polynomialFactory() {
		return polynomialFactory;
	}

	@Override
	public KeySetFactory<Primitive, PrimitivePower> monicFactory() {
		return monicFactory;
	}
}
