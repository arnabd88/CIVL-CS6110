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
package edu.udel.cis.vsl.sarl.ideal.simplify;

import static edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator.EQUALS;
import static edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator.LESS_THAN;
import static edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator.LESS_THAN_EQUALS;
import static edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator.NEQ;

import java.io.PrintStream;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import edu.udel.cis.vsl.sarl.IF.CoreUniverse;
import edu.udel.cis.vsl.sarl.IF.SARLInternalException;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Interval;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.IF.number.RationalNumber;
import edu.udel.cis.vsl.sarl.IF.object.BooleanObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
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
import edu.udel.cis.vsl.sarl.simplify.IF.Simplifier;
import edu.udel.cis.vsl.sarl.simplify.common.CommonSimplifier;

/**
 * <p>
 * An implementation of {@link Simplifier} for the "ideal" numeric factory
 * {@link IdealFactory}.
 * </p>
 *
 * <p>
 * TODO: also would like to map symbolic constants that can be solved for in
 * terms of earlier ones to expressions.
 * </p>
 */
public class IdealSimplifier extends CommonSimplifier {

	// Static fields...

	/**
	 * Print debugging information when any non-trivial simplification is
	 * performed?
	 */
	public final static boolean debugSimps = false;

	/**
	 * Print general debugging information?
	 */
	public final static boolean debug = false;

	/**
	 * Where to print debugging information.
	 */
	public final static PrintStream out = System.out;

	// Instance fields...

	/**
	 * Object that gathers together references to various objects needed for
	 * simplification.
	 */
	private SimplifierInfo info;

	/**
	 * The current assumption underlying this simplifier. Initially this is the
	 * assumption specified at construction, but it can be simplified during
	 * construction. After construction completes, it does not change. It does
	 * not include the symbolic constants occurring in the
	 * {@link #substitutionMap} as these have been replaced by their constant
	 * values. Hence: the original assumption (which is not stored) is
	 * equivalent to {@link #assumption} and {@link #substitutionMap}.
	 */
	private BooleanExpression assumption;

	/**
	 * This is the same as the {@link #assumption}, but without the information
	 * from the {@link #boundMap}, {@link #booleanMap}, {@link #constantMap},
	 * and {@link #otherConstantMap} thrown in. I.e., assumption = rawAssumption
	 * + boundMap + booleanMap + constantMap + otherConstantMap. Currently it is
	 * used only to implement the method {@link #assumptionAsInterval()}. Should
	 * probably get rid of that method and this field.
	 */
	private BooleanExpression rawAssumption;

	/**
	 * Map from symbolic constants to their "solved" values. These symbolic
	 * constants will be replaced by their corresponding values in all
	 * expressions simplified by this simplifier.
	 */
	private Map<SymbolicConstant, SymbolicExpression> substitutionMap = null;

	/**
	 * A simplified version of the context, including the substitutions.
	 */
	private BooleanExpression fullContext = null;

	/**
	 * A map that assigns bounds to monics.
	 */
	private BoundMap boundMap;

	/**
	 * A map that assigns concrete boolean values to boolean primitive
	 * expressions.
	 */
	private Map<BooleanExpression, Boolean> booleanMap = new HashMap<>();

	/**
	 * Map assigning concrete numerical values to certain {@link Monic}s.
	 */
	private Map<Monic, Number> constantMap = new HashMap<>();

	/**
	 * Map assigning concrete values to certain non-numeric expressions.
	 */
	private Map<SymbolicExpression, SymbolicExpression> otherConstantMap = new HashMap<>();

	/**
	 * Has the interval interpretation of this context been computed?
	 */
	private boolean intervalComputed = false;

	/**
	 * The interpretation of the context as an Interval, or <code>null</code> if
	 * it cannot be so interpreted.
	 */
	private Interval theInterval = null;

	/**
	 * The variable bound by the interval.
	 */
	private SymbolicConstant intervalVariable = null;

	// Constructors...

	/**
	 * Constructs new simplifier based on the given assumption. The assumption
	 * is analyzed to extract information such as bounds, and the maps which are
	 * fields of this class are populated based on that information.
	 * 
	 * @param info
	 *            the info object wrapping together references to all objects
	 *            needed for this simplifier to do its job
	 * @param assumption
	 *            the assumption ("context") on which this simplifier will be
	 *            based
	 */
	public IdealSimplifier(SimplifierInfo info, BooleanExpression assumption) {
		super(info.universe);
		this.info = info;
		this.assumption = assumption;
		this.boundMap = new BoundMap(info);
		initialize();
	}

	// private methods...

	// ****************************************************************
	// *.........................Initialization.......................*
	// *........ Extraction of information from the assumption........*
	// ****************************************************************

	/**
	 * The main initialization method: extract information from
	 * {@link #assumption} and populates the various maps and other fields of
	 * this class. This is run once, when this object is instantiated.
	 */
	private void initialize() {
		while (true) {
			// because simplifications can improve...
			clearSimplificationCache();

			boolean satisfiable = extractBounds();

			if (!satisfiable) {
				if (info.verbose) {
					info.out.println("Path condition is unsatisfiable.");
					info.out.flush();
				}
				rawAssumption = assumption = info.falseExpr;
				return;
			}

			// need to substitute into assumption new value of symbolic
			// constants.
			BooleanExpression newAssumption = (BooleanExpression) simplifyExpression(
					assumption);

			rawAssumption = newAssumption;

			// At this point, rawAssumption and newAssumption contain
			// only those facts that could not be determined from the
			// booleanMap, boundMap, constantMap, and otherConstantMap.
			// These facts need to be added back in to newAssumption---except
			// for the case where a symbolic constant is mapped to a concrete
			// value in the constantMap.
			// Such symbolic constants will be entirely eliminated from the
			// assumption.

			// After simplifyExpression, the removable symbolic constants
			// should all be gone, replaced with their concrete values.
			// However, as we add back in facts from the constant map,
			// bound map, boolean map, and other constant map,
			// those symbolic constants might sneak back in!
			// We will remove them again later.

			for (Entry<Monic, Interval> entry : boundMap.entrySet()) {
				Monic key = entry.getKey();
				Interval interval = entry.getValue();
				Number lo = interval.lower(), hi = interval.upper();

				// if this is a constant no need to add this constraint...
				if (lo != null && hi != null && lo.equals(hi)
						&& !interval.strictLower() && !interval.strictUpper())
					continue;

				BooleanExpression constraint = boundToIdeal(key, interval);
				// note that the key is simplified before forming the
				// constraint, hence information from the boundMap
				// may have been used to simplify it. really we only
				// want to apply the constantMap to it.

				if (constraint != null)
					newAssumption = info.booleanFactory.and(newAssumption,
							constraint);
			}

			// also need to add facts from constant map.
			// but can eliminate any constant values for primitives since
			// those will never occur in the state.

			for (Entry<Monic, Number> entry : constantMap.entrySet()) {
				Monic monic = entry.getKey();

				if (monic instanceof SymbolicConstant) {
					// symbolic constant: will be entirely eliminated
				} else {
					Monomial key = (Monomial) simplifyGenericExpression(monic);
					BooleanExpression constraint = info.idealFactory.equals(key,
							info.idealFactory.constant(entry.getValue()));

					newAssumption = info.booleanFactory.and(newAssumption,
							constraint);
				}
			}

			for (Entry<SymbolicExpression, SymbolicExpression> entry : otherConstantMap
					.entrySet()) {
				SymbolicExpression key = entry.getKey();

				if (key instanceof SymbolicConstant) {
					// symbolic constant: will be entirely eliminated
				} else {
					SymbolicExpression simplifiedKey = simplifyGenericExpression(
							key);
					BooleanExpression constraint = info.universe
							.equals(simplifiedKey, entry.getValue());

					newAssumption = info.booleanFactory.and(newAssumption,
							constraint);
				}
			}

			for (Entry<BooleanExpression, Boolean> entry : booleanMap
					.entrySet()) {
				BooleanExpression primitive = entry.getKey();

				if (primitive instanceof SymbolicConstant) {
					// symbolic constant: will be entirely eliminated
				} else {
					BooleanExpression simplifiedPrimitive = (BooleanExpression) simplifyGenericExpression(
							primitive);

					newAssumption = info.booleanFactory.and(newAssumption,
							entry.getValue() ? simplifiedPrimitive
									: info.booleanFactory
											.not(simplifiedPrimitive));
				}
			}

			// substitute constant values for symbolic constants...

			Map<SymbolicExpression, SymbolicExpression> substitutionMap = new HashMap<>();

			for (Entry<Monic, Number> entry : constantMap.entrySet()) {
				SymbolicExpression key = entry.getKey();

				if (key.operator() == SymbolicOperator.SYMBOLIC_CONSTANT)
					substitutionMap.put(key, universe.number(entry.getValue()));
			}
			for (Entry<SymbolicExpression, SymbolicExpression> entry : otherConstantMap
					.entrySet()) {
				SymbolicExpression key = entry.getKey();

				if (key.operator() == SymbolicOperator.SYMBOLIC_CONSTANT)
					substitutionMap.put(key, entry.getValue());
			}
			newAssumption = (BooleanExpression) universe
					.mapSubstituter(substitutionMap).apply(newAssumption);

			// check for stabilization...
			if (assumption.equals(newAssumption))
				break;
			assumption = (BooleanExpression) universe.canonic(newAssumption);
		}
		extractRemainingFacts();
	}

	/**
	 * Produces an expression equivalent to the claim that <code>monic</code>
	 * lies in <code>interval</code>, using simplifications supported by the
	 * current {@link #assumption}. Returns <code>null</code> if
	 * <code>interval</code> is (-&infin;,&infin;). Note that the "variable" (
	 * <code>monic</code>) is simplified using method
	 * {@link #apply(SymbolicExpression)}.
	 * 
	 * @param monic
	 *            a non-<code>null</code> {@link Monic}
	 * @param interval
	 *            a non-<code>null</code> {@link Interval} of same type as
	 *            <code>monic</code>
	 * @return <code>null</code> if <code>interval</code> is (-&infin;,&infin;),
	 *         else a {@link BooleanExpression} equivalent to the statement that
	 *         <code>monic</code> lies in <code>interval</code>
	 */
	private BooleanExpression boundToIdeal(Monic monic, Interval interval) {
		Number lower = interval.lower(), upper = interval.upper();
		BooleanExpression result = null;
		Monomial ideal = (Monomial) apply(monic);

		if (lower != null) {
			if (interval.strictLower())
				result = info.idealFactory
						.lessThan(info.idealFactory.constant(lower), ideal);
			else
				result = info.idealFactory.lessThanEquals(
						info.idealFactory.constant(lower), ideal);
		}
		if (upper != null) {
			BooleanExpression upperResult;

			if (interval.strictUpper())
				upperResult = info.idealFactory.lessThan(ideal,
						info.idealFactory.constant(upper));
			else
				upperResult = info.idealFactory.lessThanEquals(ideal,
						info.idealFactory.constant(upper));
			if (result == null)
				result = upperResult;
			else
				result = info.booleanFactory.and(result, upperResult);
		}
		return result;
	}

	/**
	 * Attempts to determine bounds (upper and lower) on {@link Monic}
	 * expressions by examining the {@link #assumption}. Returns
	 * <code>false</code> if {@link assumption} is determined to be
	 * unsatisfiable. Updates {@link #boundMap}, {@link #booleanMap},
	 * {@link #constantMap}, and {@link #otherConstantMap}.
	 */
	private boolean extractBounds() {
		if (assumption.operator() == SymbolicOperator.AND) {
			for (SymbolicObject arg : assumption.getArguments()) {
				BooleanExpression clause = (BooleanExpression) arg;

				if (!extractBoundsOr(clause, boundMap, booleanMap))
					return false;
			}
		} else if (!extractBoundsOr(assumption, boundMap, booleanMap))
			return false;
		return updateConstantMap();
	}

	/**
	 * 
	 * @param poly
	 * @param value
	 */
	private void processHerbrandCast(Monomial poly, Number value) {
		if (poly.operator() == SymbolicOperator.CAST) {
			SymbolicType type = poly.type();
			SymbolicExpression original = (SymbolicExpression) poly.argument(0);
			SymbolicType originalType = original.type();

			if (originalType.isHerbrand() && originalType.isInteger()
					&& type.isInteger()
					|| originalType.isReal() && type.isReal()) {
				SymbolicExpression constant = universe.cast(originalType,
						universe.number(value));

				cacheSimplification(original, constant);
			}
		}
	}

	private boolean updateConstantMap() {
		// The constant map doesn't get cleared because we want to keep
		// accumulating facts. Thus the map might not be empty at this point.
		for (Entry<Monic, Interval> entry : boundMap.entrySet()) {
			Interval interval = entry.getValue();
			Number lower = interval.lower();

			if (lower != null && lower.equals(interval.upper())) {
				Monic expression = entry.getKey();

				assert !interval.strictLower() && !interval.strictUpper();
				constantMap.put(expression, lower);
				processHerbrandCast(expression, lower);
			}
		}

		boolean satisfiable = LinearSolver.reduceConstantMap(info.idealFactory,
				constantMap);

		if (debug) {
			printBoundMap(info.out);
			printConstantMap(info.out);
			printBooleanMap(info.out);
		}
		return satisfiable;
	}

	private void printBoundMap(PrintStream out) {
		out.println("Bound map:");
		boundMap.print(out);
	}

	private void printConstantMap(PrintStream out) {
		out.println("Constant map:");
		for (Entry<Monic, Number> entry : constantMap.entrySet()) {
			out.print(entry.getKey() + " = ");
			out.println(entry.getValue());
		}
		out.println();
		out.flush();
	}

	private void printBooleanMap(PrintStream out) {
		out.println("Boolean map:");
		for (Entry<BooleanExpression, Boolean> entry : booleanMap.entrySet()) {
			out.print(entry.getKey() + " = ");
			out.println(entry.getValue());
		}
		out.println();
		out.flush();
	}

	@SuppressWarnings("unchecked")
	private Map<BooleanExpression, Boolean> copyBooleanMap(
			Map<BooleanExpression, Boolean> map) {
		return (Map<BooleanExpression, Boolean>) (((HashMap<?, ?>) map)
				.clone());
	}

	// TODO: why not combine the boolean map into the BoundMap
	// and call it Interpretation?
	// make some of the code below methods

	private boolean extractBoundsOr(BooleanExpression or, BoundMap aBoundMap,
			Map<BooleanExpression, Boolean> aBooleanMap) {
		SymbolicOperator op = or.operator();

		if (op == SymbolicOperator.OR) {
			// p & (q0 | ... | qn) = (p & q0) | ... | (p & qn)
			// copies of original maps, corresponding to p. these never
			// change...
			BoundMap originalBoundMap = aBoundMap.clone();
			Map<BooleanExpression, Boolean> originalBooleanMap = copyBooleanMap(
					aBooleanMap);
			Iterator<? extends SymbolicObject> clauses = or.getArguments()
					.iterator();
			boolean satisfiable = extractBoundsBasic(
					(BooleanExpression) clauses.next(), aBoundMap, aBooleanMap);

			// result <- p & q0:
			// result <- result | ((p & q1) | ... | (p & qn)) :
			while (clauses.hasNext()) {
				BooleanExpression clause = (BooleanExpression) clauses.next();
				BoundMap newBoundMap = originalBoundMap.clone();
				Map<BooleanExpression, Boolean> newBooleanMap = copyBooleanMap(
						originalBooleanMap);
				// compute p & q_i:
				boolean newSatisfiable = extractBoundsBasic(clause, newBoundMap,
						newBooleanMap);

				// result <- result | (p & q_i) where result is (aBoundMap,
				// aBooleanMap)....
				satisfiable = satisfiable || newSatisfiable;
				if (newSatisfiable) {
					LinkedList<Monic> boundRemoveList = new LinkedList<>();
					LinkedList<BooleanExpression> booleanRemoveList = new LinkedList<>();

					for (Entry<Monic, Interval> entry : aBoundMap.entrySet()) {
						Monic primitive = entry.getKey();
						Interval oldBound = entry.getValue();
						Interval newBound = newBoundMap.get(primitive);

						if (newBound == null) {
							boundRemoveList.add(primitive);
						} else {
							newBound = info.numberFactory.join(oldBound,
									newBound);
							if (!oldBound.equals(newBound)) {
								if (newBound.isUniversal())
									boundRemoveList.add(primitive);
								else
									entry.setValue(newBound);
							}
						}
					}
					for (Monic primitive : boundRemoveList)
						aBoundMap.remove(primitive);
					for (Entry<BooleanExpression, Boolean> entry : aBooleanMap
							.entrySet()) {
						BooleanExpression primitive = entry.getKey();
						Boolean oldValue = entry.getValue();
						Boolean newValue = newBooleanMap.get(primitive);

						if (newValue == null || !newValue.equals(oldValue))
							booleanRemoveList.add(primitive);
					}
					for (BooleanExpression primitive : booleanRemoveList)
						aBooleanMap.remove(primitive);
				}
			}
			return satisfiable;
		} else { // 1 clause
			// if this is of the form EQ x,y where y is a constant and
			// x and y are not-numeric, add to otherConstantMap
			if (op == SymbolicOperator.EQUALS) {
				SymbolicExpression arg0 = (SymbolicExpression) or.argument(0),
						arg1 = (SymbolicExpression) or.argument(1);
				SymbolicType type = arg0.type();

				if (!type.isNumeric()) {
					boolean const0 = arg0
							.operator() == SymbolicOperator.CONCRETE;
					boolean const1 = (arg1
							.operator() == SymbolicOperator.CONCRETE);

					if (const1 && !const0) {
						otherConstantMap.put(arg0, arg1);
						return true;
					} else if (const0 && !const1) {
						otherConstantMap.put(arg1, arg0);
						return true;
					} else if (const0 && const1) {
						return arg0.equals(arg1);
					} else {
						return true;
					}
				}
			}
			return extractBoundsBasic(or, aBoundMap, aBooleanMap);
		}
	}

	/**
	 * A basic expression is either a boolean constant (true/false), a
	 * LiteralExpression (p or !p) or QuantifierExpression
	 */
	private boolean extractBoundsBasic(BooleanExpression basic,
			BoundMap aBoundMap, Map<BooleanExpression, Boolean> aBooleanMap) {
		SymbolicOperator operator = basic.operator();

		if (operator == SymbolicOperator.CONCRETE)
			return ((BooleanObject) basic.argument(0)).getBoolean();
		if (isRelational(operator)) {

			// Cases: 0=Primitive, 0<Monic, 0<=Monic, Monic<0, Monic<=0,
			// 0!=Primitive.

			SymbolicExpression arg0 = (SymbolicExpression) basic.argument(0);
			SymbolicExpression arg1 = (SymbolicExpression) basic.argument(1);

			if (arg0.type().isNumeric()) {
				switch (operator) {
				case EQUALS: // 0==x
					return extractEQ0Bounds((Primitive) arg1, aBoundMap,
							aBooleanMap);
				case NEQ:
					return extractNEQ0Bounds((Primitive) arg1, aBoundMap,
							aBooleanMap);
				case LESS_THAN: // 0<x or x<0
				case LESS_THAN_EQUALS: // 0<=x or x<=0
					if (arg0.isZero()) {
						return extractIneqBounds((Monic) arg1, true,
								operator == LESS_THAN, aBoundMap, aBooleanMap);
					} else {
						return extractIneqBounds((Monic) arg0, false,
								operator == LESS_THAN, aBoundMap, aBooleanMap);
					}
				default:
					throw new SARLInternalException(
							"Unknown RelationKind: " + operator);
				}
			}
		} else if (operator == SymbolicOperator.EXISTS
				|| operator == SymbolicOperator.FORALL) {
			// TODO: forall and exists are difficult
			// forall x: can substitute whatever you want for x
			// and extract bounds.
			// example: forall i: a[i]<7. Look for all occurrences of a[*]
			// and add bounds
			return true;
		} else if (operator == SymbolicOperator.NOT) {
			BooleanExpression primitive = (BooleanExpression) basic.argument(0);
			Boolean value = aBooleanMap.get(primitive);

			if (value != null)
				return !value;
			aBooleanMap.put(primitive, false);
			return true;
		}

		Boolean value = aBooleanMap.get(basic);

		if (value != null)
			return value;
		aBooleanMap.put(basic, true);
		return true;
	}

	private boolean extractEQ0Bounds(Primitive primitive, BoundMap aBoundMap,
			Map<BooleanExpression, Boolean> aBooleanMap) {
		if (primitive instanceof Polynomial)
			return extractEQ0BoundsPoly((Polynomial) primitive, aBoundMap,
					aBooleanMap);

		NumberFactory nf = info.numberFactory;
		Interval bound = aBoundMap.get(primitive);
		Number zero = primitive.type().isInteger() ? nf.zeroInteger()
				: nf.zeroRational();

		if (bound != null && !bound.contains(zero))
			return false;
		aBoundMap.set(primitive, zero);
		return true;
	}

	/**
	 * Given the fact that poly==0, for some {@link Polynomial} poly, updates
	 * the specified bound map and boolean map appropriately.
	 * 
	 * @param poly
	 *            a non-<code>null</code> polynomial
	 * @param aBoundMap
	 *            a bound map: a map from pseudo-primitive polynomials to bound
	 *            objects specifying an interval bound for those polynomials
	 * @param aBooleanMap
	 *            a map specifying a concrete boolean value for some set of
	 *            boolean-valued symbolic expressions
	 * @return <code>false</code> if it is determined that the given assertion
	 *         is inconsistent with the information in the bound map and boolean
	 *         map; else <code>true</code>
	 */
	private boolean extractEQ0BoundsPoly(Polynomial poly, BoundMap aBoundMap,
			Map<BooleanExpression, Boolean> aBooleanMap) {
		NumberFactory nf = info.numberFactory;
		AffineExpression affine = info.affineFactory.affine(poly);
		Monic pseudo = affine.pseudo();
		RationalNumber coefficient = nf.rational(affine.coefficient());
		RationalNumber offset = nf.rational(affine.offset());
		RationalNumber rationalValue = nf
				.negate(info.numberFactory.divide(offset, coefficient));
		Number value; // same as rationalValue but IntegerNumber if type is
						// integer
		Interval bound = aBoundMap.get(pseudo);

		if (pseudo.type().isInteger()) {
			if (!nf.isIntegral(rationalValue))
				return false;
			value = nf.integerValue(rationalValue);
		} else {
			value = rationalValue;
		}
		if (bound != null && !bound.contains(value))
			return false;
		aBoundMap.set(pseudo, value);
		return true;
	}

	private boolean extractNEQ0Bounds(Primitive primitive, BoundMap aBoundMap,
			Map<BooleanExpression, Boolean> aBooleanMap) {

		if (primitive instanceof Polynomial)
			return extractNEQ0BoundsPoly((Polynomial) primitive, aBoundMap,
					aBooleanMap);

		Interval bound = aBoundMap.get(primitive);
		SymbolicType type = primitive.type();
		Constant zero = info.idealFactory.zero(type);

		if (bound == null) {
			// for now, nothing can be done, since the bounds are
			// plain intervals. we need a more precise abstraction
			// than intervals here.
		} else if (bound.contains(zero.number())) {
			NumberFactory nf = info.numberFactory;
			Interval oldBound = bound;

			// is value an end-point? Might be able to sharpen bound...
			if (bound.lower() != null && bound.lower().isZero()
					&& !bound.strictLower())
				bound = nf.restrictLower(bound, bound.lower(), true);
			if (bound.upper() != null && bound.upper().isZero()
					&& !bound.strictUpper())
				bound = nf.restrictUpper(bound, bound.upper(), true);
			if (bound.isEmpty())
				return false;
			if (!bound.equals(oldBound))
				aBoundMap.set(primitive, bound);
		}
		aBooleanMap.put(info.universe.neq(zero, primitive), true);
		return true;
	}

	/**
	 * Given the fact that poly!=0, for some {@link Polynomial} poly, updates
	 * the specified bound map and boolean map appropriately.
	 * 
	 * @param poly
	 *            a non-<code>null</code> polynomial
	 * @param aBoundMap
	 *            a bound map: a map from pseudo-primitive polynomials to bound
	 *            objects specifying an interval bound for those polynomials
	 * @param aBooleanMap
	 *            a map specifying a concrete boolean value for some set of
	 *            boolean-valued symbolic expressions
	 * @return <code>false</code> if it is determined that the given assertion
	 *         is inconsistent with the information in the bound map and boolean
	 *         map; else <code>true</code>
	 */
	private boolean extractNEQ0BoundsPoly(Polynomial poly, BoundMap aBoundMap,
			Map<BooleanExpression, Boolean> aBooleanMap) {
		// poly=aX+b. if X=-b/a, contradiction.
		NumberFactory nf = info.numberFactory;
		SymbolicType type = poly.type();
		AffineExpression affine = info.affineFactory.affine(poly);
		Monic pseudo = affine.pseudo();
		RationalNumber coefficient = nf.rational(affine.coefficient());
		RationalNumber offset = nf.rational(affine.offset());
		RationalNumber rationalValue = nf
				.negate(nf.divide(offset, coefficient));
		Number value; // same as rationalValue but IntegerNumber if type is
						// integer
		Interval bound = aBoundMap.get(pseudo);
		Monomial zero = info.idealFactory.zero(type);

		if (type.isInteger()) {
			if (nf.isIntegral(rationalValue)) {
				value = nf.integerValue(rationalValue);
			} else {
				// an integer cannot equal a non-integer.
				aBooleanMap.put(info.idealFactory.neq(zero, poly), true);
				return true;
			}
		} else {
			value = rationalValue;
		}
		// interpret fact pseudo!=value, where pseudo is in bound
		if (bound == null) {
			// TODO:
			// for now, nothing can be done, since the bounds are
			// plain intervals. we need a more precise abstraction
			// than intervals here, like Range.
		} else if (bound.contains(value)) {
			Interval oldBound = bound;

			// is value an end-point? Might be able to sharpen bound...
			if (bound.lower() != null && bound.lower().equals(value)
					&& !bound.strictLower())
				bound = nf.restrictLower(bound, bound.lower(), true);
			if (bound.upper() != null && bound.upper().equals(value)
					&& !bound.strictUpper())
				bound = nf.restrictUpper(bound, bound.upper(), true);
			if (bound.isEmpty())
				return false;
			if (!bound.equals(oldBound))
				aBoundMap.set(pseudo, bound);
		}
		aBooleanMap.put(info.universe.neq(zero, poly), true);
		return true;
	}

	private boolean extractIneqBounds(Monic monic, boolean gt, boolean strict,
			BoundMap aBoundMap, Map<BooleanExpression, Boolean> aBooleanMap) {
		if (monic instanceof Polynomial)
			return extractIneqBoundsPoly((Polynomial) monic, gt, strict,
					aBoundMap, aBooleanMap);

		NumberFactory nf = info.numberFactory;
		Number zero = monic.type().isInteger() ? nf.zeroInteger()
				: nf.zeroRational();
		Interval interval = gt ? aBoundMap.restrictLower(monic, zero, strict)
				: aBoundMap.restrictUpper(monic, zero, strict);

		return !interval.isEmpty();
	}

	private boolean extractIneqBoundsPoly(Polynomial poly, boolean gt,
			boolean strict, BoundMap aBoundMap,
			Map<BooleanExpression, Boolean> aBooleanMap) {
		AffineExpression affine = info.affineFactory.affine(poly);
		Monic pseudo = affine.pseudo();
		Number coefficient = affine.coefficient();
		boolean pos = coefficient.signum() > 0;
		Number theBound = info.affineFactory.bound(affine, gt, strict);
		Interval interval;

		// aX+b>0.
		// a>0:lower bound (X>-b/a).
		// a<0: upper bound (X<-b/a).
		assert pseudo != null;
		if (poly.type().isInteger())
			strict = false;
		if ((pos && gt) || (!pos && !gt)) // lower bound
			interval = aBoundMap.restrictLower(pseudo, theBound, strict);
		else
			// upper bound
			interval = aBoundMap.restrictUpper(pseudo, theBound, strict);
		return !interval.isEmpty();
	}

	private void declareFact(SymbolicExpression booleanExpression,
			boolean truth) {
		BooleanExpression value = truth ? info.trueExpr : info.falseExpr;

		cacheSimplification(booleanExpression, value);
	}

	private void declareClauseFact(BooleanExpression clause) {
		if (isNumericRelational(clause)) {
			if (clause.operator() == SymbolicOperator.NEQ) {
				BooleanExpression eq0 = (BooleanExpression) info.universe
						.not(clause);

				declareFact(eq0, false);
			}
		} else
			declareFact(clause, true);
	}

	/**
	 * This method inserts into the simplification cache all facts from the
	 * assumption that are not otherwise encoded in the {@link #constantMap},
	 * {@link #booleanMap}, or {@link #boundMap}. It is to be invoked only after
	 * the assumption has been simplified for the final time.
	 */
	private void extractRemainingFacts() {
		SymbolicOperator operator = assumption.operator();

		if (operator == SymbolicOperator.AND) {
			for (SymbolicObject arg : assumption.getArguments()) {
				declareClauseFact((BooleanExpression) arg);
			}
		} else {
			declareClauseFact(assumption);
		}
	}

	// ****************************************************************
	// * ................. Simplification Routines................... *
	// ****************************************************************

	/**
	 * Build up entries in power map from the monic factors.
	 * 
	 * @param powerMap
	 *            map from the primitives to the exponent assigned to that
	 *            primitive in the final result
	 * @param positive
	 *            if true, exponents should be added to the entries in powerMap,
	 *            otherwise they should be subtracted from entries
	 * @param monic
	 * 
	 * @return true iff change occurred
	 */
	private boolean simplifyPowers(Map<Primitive, RationalExpression> powerMap,
			boolean positive, Monic monic) {
		IdealFactory idf = info.idealFactory;
		PrimitivePower[] factors = monic.monicFactors(idf);
		boolean isInteger = monic.type().isInteger();
		boolean change = false;
		NumberFactory nf = info.numberFactory;

		for (PrimitivePower pp : factors) {
			Primitive primitive = pp.primitive(idf);
			int outerExponent = pp.primitivePowerExponent(idf).getInt();
			IntegerNumber signedOuterExponent = nf
					.integer(positive ? outerExponent : -outerExponent);
			RationalExpression realSignedOuterExponent = idf
					.constant(isInteger ? signedOuterExponent
							: nf.integerToRational(signedOuterExponent));
			RationalExpression newExponent;
			Primitive base;

			if (primitive.operator() == SymbolicOperator.POWER) {
				base = (Primitive) primitive.argument(0);
				newExponent = idf.multiply(realSignedOuterExponent,
						(RationalExpression) primitive.argument(1));
				change = change || outerExponent != Math
						.abs(idf.getConcreteExponent(newExponent).intValue());
			} else {
				base = primitive;
				newExponent = realSignedOuterExponent;
			}

			NumericExpression oldExponent = powerMap.get(base);

			if (oldExponent == null) {
				powerMap.put(base, newExponent);
			} else {
				powerMap.put(base, idf.add(oldExponent, newExponent));
				change = true;
			}
		}
		return change;
	}

	/**
	 * Simplifies any {@link SymbolicOperator#POWER} operations occurring in a
	 * rational expression.
	 * 
	 * @param rational
	 *            a rational expression
	 * @return equivalent rational expression in which power operations that can
	 *         be combined are combined or simplified
	 */
	private RationalExpression simplifyPowersRational(
			RationalExpression rational) {
		IdealFactory idf = info.idealFactory;
		Monomial numerator = rational.numerator(idf),
				denominator = rational.denominator(idf);
		Monic m1 = numerator.monic(idf), m2 = denominator.monic(idf);
		Map<Primitive, RationalExpression> powerMap = new HashMap<>();
		boolean change1 = simplifyPowers(powerMap, true, m1);
		boolean change2 = simplifyPowers(powerMap, false, m2);

		if (change1 || change2) {
			RationalExpression result = idf.one(rational.type());

			for (Entry<Primitive, RationalExpression> entry : powerMap
					.entrySet()) {
				result = idf.multiply(result,
						idf.power(entry.getKey(), entry.getValue()));
			}
			result = idf.divide(
					idf.multiply(result, numerator.monomialConstant(idf)),
					denominator.monomialConstant(idf));
			return result;
		}
		return rational;
	}

	/**
	 * Simplifies a {@link Monic} that is not a {@link Polynomial}.
	 * 
	 * Strategy: look up in {@link #constantMap}. If found, great. Otherwise try
	 * generic simplification.
	 * 
	 * @param monic
	 *            a non-<code>null</code> {@link Monic} which is not an instance
	 *            of {@link Polynomial}.
	 * 
	 * @return a simplified version of <code>monic</code> which is equivalent to
	 *         <code>monic</code> under the current assumptions
	 */
	private Monomial simplifyMonic(Monic monic) {
		assert !(monic instanceof Polynomial);

		Number constant = constantMap.get(monic);

		if (constant != null)
			return info.idealFactory.constant(constant);
		return (Monomial) super.simplifyGenericExpression(monic);
	}

	@SuppressWarnings("unused")
	private Monomial simplifyPolynomial2(Polynomial poly) {
		IdealFactory id = info.idealFactory;

		Number constant = constantMap.get(poly);

		if (constant != null)
			return id.constant(constant);

		// try rewriting poly as aX+b for some pseudo monomial X...
		AffineExpression affine = info.affineFactory.affine(poly);

		if (!affine.coefficient().isOne() || !affine.offset().isZero()) {
			constant = constantMap.get(affine.pseudo());
			if (constant != null)
				return id.constant(
						info.affineFactory.affineValue(affine, constant));
		}

		Monomial[] termMap = poly.termMap(id);
		int size = termMap.length;
		Monomial[] terms = new Monomial[size];
		boolean simplified = false;

		for (int i = 0; i < size; i++) {
			Monomial term = termMap[i];

			if (debug) {
				out.println("Simplifying term " + i + " of poly " + poly.id());
				out.flush();
			}

			Monomial simplifiedTerm = (Monomial) apply(term);

			if (debug) {
				out.println("Simplification of term " + i + " of poly "
						+ poly.id() + " complete");
				out.flush();
			}

			simplified = simplified || term != simplifiedTerm;
			terms[i] = simplifiedTerm;
		}

		if (debug) {
			out.println("Adding simplified monomials of poly " + poly.id());
			out.flush();
		}

		Monomial result = simplified ? id.addMonomials(terms) : poly;

		if (debug) {
			out.println("Completed addition of simplified monomials of poly "
					+ poly.id());
			out.flush();
		}

		return result;
	}

	/**
	 * <p>
	 * Simplifies a {@link Polynomial}. Note that method
	 * {@link #simplifyGenericExpression(SymbolicExpression)} cannot be used,
	 * since that method will invoke
	 * {@link CoreUniverse#make(SymbolicOperator, SymbolicType, SymbolicObject[])}
	 * , which will apply binary addition repeatedly on the terms of a
	 * {@link Polynomial}, which will not result in the correct form.
	 * </p>
	 * 
	 * <p>
	 * The following strategies are used:
	 * <ul>
	 * <li>look up the polynomial in the {@link #constantMap}</li>
	 * <li>convert to an {@link AffineExpression} and look for a constant value
	 * of the pseudo</li>
	 * <li>simplify the individual terms and sum the results</li>
	 * <li>full expand the polynomial</li>
	 * </ul>
	 * The process is repeated until it stabilizes or a constant value is
	 * determined.
	 * </p>
	 * 
	 * @param poly
	 *            a {@link Polynomial} with at least 2 terms
	 * @return a simplified version of <code>poly</code> equivalent to
	 *         <code>poly</code> under the existing assumptions
	 */
	private Monomial simplifyPolynomial(Polynomial poly) {
		IdealFactory id = info.idealFactory;

		while (true) { // repeat until stabilization
			Number constant = constantMap.get(poly);

			if (constant != null)
				return id.constant(constant);

			// try rewriting poly as aX+b for some pseudo monomial X...
			AffineExpression affine = info.affineFactory.affine(poly);

			if (!affine.coefficient().isOne() || !affine.offset().isZero()) {
				constant = constantMap.get(affine.pseudo());
				if (constant != null)
					return id.constant(
							info.affineFactory.affineValue(affine, constant));
			}

			if (debug) {
				// out.println("simplifyPoly: starting term simplification of "
				// + poly.id());
				// TODO: need toString method which will check how long the
				// description is and cut it off and use a different description
				// instead.
				out.flush();
			}

			Monomial[] termMap = poly.termMap(id);
			int size = termMap.length;
			Monomial[] terms = new Monomial[size];
			boolean simplified = false;

			for (int i = 0; i < size; i++) {
				Monomial term = termMap[i];
				Monomial simplifiedTerm = (Monomial) apply(term);

				simplified = simplified || term != simplifiedTerm;
				terms[i] = simplifiedTerm;
			}

			Monomial result = simplified ? id.addMonomials(terms) : poly;

			// can't decide whether to expand or not.
			// For now, only expanding for "=0"...
			if (result == poly)
				return result;
			if (!(result instanceof Polynomial))
				return (Monomial) apply(result);
			if (debug) {
				// out.println("simplifyPoly: poly = " + poly);
				// out.println("simplifyPoly: result = " + result);
			}
			poly = (Polynomial) id.objectFactory().canonic(result);
		}
	}

	/**
	 * Determines if the operator is one of the relation operators
	 * {@link SymbolicOperator#LESS_THAN},
	 * {@link SymbolicOperator#LESS_THAN_EQUALS},
	 * {@link SymbolicOperator#EQUALS}, or {@link SymbolicOperator#NEQ}.
	 * 
	 * @param operator
	 *            a non-<code>null</code> symbolic operator
	 * @return <code>true</code> iff <code>operator</code> is one of the four
	 *         relationals
	 */
	private boolean isRelational(SymbolicOperator operator) {
		switch (operator) {
		case LESS_THAN:
		case LESS_THAN_EQUALS:
		case EQUALS:
		case NEQ:
			return true;
		default:
			return false;
		}
	}

	/**
	 * Determines whether the expression is a numeric relational expression,
	 * i.e., the operator is one of the four relation operators and argument 0
	 * has numeric type.
	 * 
	 * @param expression
	 *            any non-<code>null</code> symbolic expression
	 * @return <code>true</code> iff the expression is relational with numeric
	 *         arguments
	 */
	private boolean isNumericRelational(SymbolicExpression expression) {
		return isRelational(expression.operator())
				&& ((SymbolicExpression) expression.argument(0)).isNumeric();
	}

	/**
	 * Simplifies a relational expression. Assumes expression does not already
	 * exist in simplification cache. Does NOT assume that generic
	 * simplification has been performed on expression. Current strategy:
	 * 
	 * <pre>
	 * 1. simplifyGeneric
	 * 2. if no change: simplifyRelationalWork
	 * 3. otherwise (change): if concrete, finished
	 * 4. otherwise (change, not concrete): look up in cache
	 * 5. if found in cache, finished
	 * 6. otherwise (change, not concrete, not cached): if relational,
	 *    simplifyRelationalWork
	 * 7. otherwise (change, not concrete, not cached, not relational):
	 *    simplifyGeneric
	 * </pre>
	 * 
	 * @param expression
	 *            any boolean expression
	 * @return simplified version of the expression, which may be the original
	 *         expression
	 */
	private BooleanExpression simplifyRelational(BooleanExpression expression) {
		BooleanExpression result1 = (BooleanExpression) simplifyGenericExpression(
				expression); // to
								// substitute
								// constants,
								// etc.

		if (result1 == expression)
			return simplifyRelationalWork(expression);
		if (result1.operator() == SymbolicOperator.CONCRETE)
			return result1;

		BooleanExpression result2 = (BooleanExpression) getCachedSimplification(
				result1);

		if (result2 != null)
			return result2;
		if (isRelational(result1.operator()))
			return simplifyRelationalWork(result1);
		return (BooleanExpression) simplifyGenericExpression(result1);
	}

	/**
	 * Simplifies a relational expression. Assumes expression has already gone
	 * through generic simplification and result is not in cache.
	 * 
	 * @param expression
	 *            a relation expression, i.e., one in which the operator is one
	 *            of &lt;, &le;, =, &ne;.
	 * @return possibly simplified version of <code>expression</code>
	 */
	private BooleanExpression simplifyRelationalWork(
			BooleanExpression expression) {
		SymbolicOperator operator = expression.operator();
		Monomial arg0 = (Monomial) expression.argument(0),
				arg1 = (Monomial) expression.argument(1);
		BooleanExpression result;

		// 0=Primitive, 0<Monic, 0<=Monic, Monic<0, Monic<=0, 0!=Primitive.

		switch (operator) {
		case LESS_THAN:
		case LESS_THAN_EQUALS: {
			boolean strict = operator == SymbolicOperator.LESS_THAN;

			if (arg0.isZero()) {// 0<?arg1
				result = simplifyIneq0((Monic) arg1, true, strict);
			} else if (arg1.isZero()) {
				result = simplifyIneq0((Monic) arg0, false, strict);
			} else
				throw new SARLInternalException(
						"unreachable: impossible expression " + expression);
			if (result == null) {
				return expression;
			} else {
				if (debugSimps) {
					out.println("Simplify ineq input:  " + expression);
					out.println("Simplify ineq result: " + result);
					out.flush();
				}
				return result;
			}
		}
		case EQUALS: {
			assert arg0.isZero();
			// arg1 has already been simplified by apply()
			result = simplifyEQ0((Primitive) arg1);
			if (result == null) {
				return expression;
			} else {
				if (debugSimps) {
					out.println("Simplify EQ0 input : " + expression);
					out.println("Simplify EQ0 result: " + result);
					out.flush();
				}
				return result;
			}
		}
		case NEQ: {
			assert arg0.isZero();

			BooleanExpression negExpression = universe.not(expression);

			result = (BooleanExpression) simplifyExpression(negExpression);
			result = universe.not(result);
			return result;
		}
		default:
			throw new SARLInternalException("unreachable");
		}
	}

	/**
	 * Computes a simplified version of the expression <code>monic</code>=0.
	 * 
	 * @param monic
	 *            a non-<code>null</code> {@link Monic}
	 * @return simplified expression equivalent to <code>monic</code>=0
	 */
	private BooleanExpression simplifiedEQ0Monic(Monic monic) {
		NumericExpression zero = info.idealFactory.zero(monic.type());
		BooleanExpression expr = info.idealFactory.equals(zero, monic);
		BooleanExpression result = (BooleanExpression) simplifyExpression(expr);

		return result;
	}

	/**
	 * Computes a simplified version of the expression <code>monic</code>&ne;0.
	 * 
	 * @param monic
	 *            a non-<code>null</code> {@link Monic}
	 * @return simplified expression equivalent to <code>monic</code>&ne;0
	 */
	private BooleanExpression simplifiedNEQ0Monic(Monic monic) {
		NumericExpression zero = info.idealFactory.zero(monic.type());
		BooleanExpression expr = info.idealFactory.neq(zero, monic);
		BooleanExpression result = (BooleanExpression) simplifyExpression(expr);

		return result;
	}

	/**
	 * A categorization of intervals based on their relationship to 0. Every
	 * interval falls into exactly one of these categories.
	 * 
	 * @author siegel
	 */
	private enum BoundType {
		/**
		 * Every element of the interval is less than 0 and the interval is not
		 * empty.
		 */
		LT0,
		/**
		 * Every element of the interval is less than or equal to 0 and the
		 * interval contains 0 and a negative number.
		 */
		LE0,
		/** The interval consists exactly of 0 and nothing else. */
		EQ0,
		/**
		 * The interval contains 0 and a positive number and every element of
		 * the interval is greater than or equal to 0.
		 */
		GE0,
		/**
		 * Every element of the interval is greater than 0 and the interval is
		 * non-empty.
		 */
		GT0,
		/** The interval is empty */
		EMPTY,
		/** The interval contains a negative number, 0, and a positive number */
		ALL
	};

	/**
	 * Computes the bound type of the given {@link Interval}.
	 * 
	 * @param interval
	 *            a non-<code>null</code> {@link Interval}
	 * @return the unique category (instance of {@link BoundType}) into which
	 *         <code>interval</code> falls
	 */
	private BoundType boundType(Interval interval) {
		if (interval.isEmpty())
			return BoundType.EMPTY;

		Number l = interval.lower(), r = interval.upper();
		int lsign = l == null ? -1 : l.signum();
		int rsign = r == null ? 1 : r.signum();

		if (lsign > 0)
			return BoundType.GT0;
		if (rsign < 0)
			return BoundType.LT0;

		if (lsign < 0) {
			if (rsign == 0) {
				return interval.strictUpper() ? BoundType.LT0 : BoundType.LE0;
			} else { // rsign > 0
				return BoundType.ALL;
			}
		} else { // lsign == 0
			if (rsign == 0) {
				return BoundType.EQ0;
			} else { // rsign > 0
				return interval.strictLower() ? BoundType.GT0 : BoundType.GE0;
			}
		}
	}

	/**
	 * Given the fact that x is in the set specified by the {@link BoundType}
	 * <code>bt</code>, attempts to compute a simplified version of the
	 * expression "monic OP 0", where OP is one of le, lt, gt, or ge. Returns
	 * <code>null</code> if no simplified version is possible.
	 * 
	 * @param monic
	 * @param bt
	 * @param gt
	 * @param strict
	 * @return
	 */
	private BooleanExpression ineqFromBoundType(Monic monic, BoundType bt,
			boolean gt, boolean strict) {
		switch (bt) {
		case ALL:
			return null;
		case EMPTY:
			return info.trueExpr;
		case EQ0:
			return strict ? info.falseExpr : info.trueExpr;
		case GE0:
			if (gt)
				return strict ? simplifiedNEQ0Monic(monic) : info.trueExpr;
			else
				return strict ? info.falseExpr : simplifiedEQ0Monic(monic);
		case GT0:
			return gt ? info.trueExpr : info.falseExpr;
		case LE0:
			if (gt)
				return strict ? info.falseExpr : simplifiedEQ0Monic(monic);
			else
				return strict ? simplifiedNEQ0Monic(monic) : info.trueExpr;
		case LT0:
			return gt ? info.falseExpr : info.trueExpr;
		default:
			return null;
		}
	}

	private BoundType getBoundTypePower(Primitive powerExpr) {
		IdealFactory idf = info.idealFactory;
		RationalExpression base = (RationalExpression) powerExpr.argument(0);

		// if base>0, then base^exponent>0:
		if (apply(idf.isPositive(base)).isTrue())
			return BoundType.GT0;
		// if base>=0, then base^exponent>=0:
		if (apply(idf.isNonnegative(base)).isTrue())
			return BoundType.GE0;

		// if exponent is not integral or is even, base^exponent>=0:
		RationalExpression exponent = (RationalExpression) powerExpr
				.argument(1);
		Number exponentNumber = idf.extractNumber(exponent);
		NumberFactory nf = info.numberFactory;

		if (exponentNumber != null) {
			if (exponentNumber instanceof IntegerNumber) {
				IntegerNumber exponentInteger = (IntegerNumber) exponentNumber;

				if (nf.mod(exponentInteger, nf.integer(2)).isZero()) {
					return BoundType.GE0;
				}
			} else {
				if (!nf.isIntegral((RationalNumber) exponentNumber))
					return BoundType.GE0;
				else {
					IntegerNumber exponentInteger = nf
							.integerValue((RationalNumber) exponentNumber);

					if (nf.mod(exponentInteger, nf.integer(2)).isZero())
						return BoundType.GE0;
				}
			}
		}
		return null;
	}

	private BoundType getBoundTypeMonic(Monic monic) {
		if (monic.isOne())
			return BoundType.GT0;

		Interval monicBound = boundMap.get(monic);

		if (monicBound != null)
			return boundType(monicBound);

		SymbolicOperator op = monic.operator();

		if (op == SymbolicOperator.POWER) {
			return getBoundTypePower((Primitive) monic);
		}
		return null;
	}

	/**
	 * Simplifies an inequality of one of the forms: x&gt;0, x&ge;0, x&lt;0,
	 * x&le;0, where x is a {@link Monic} in which the maximum degree of any
	 * {@link Primitive} is 1. Assumes <code>monic</code> is already simplified.
	 * 
	 * @param monic
	 *            a non-<code>null</code>, simplified, {@link Monic}
	 * @param gt
	 *            is the condition one of x&gt;0 or x&ge;0 (i.e., not x&lt;0 or
	 *            x&le;0)
	 * @param strict
	 *            is the form one of x&gt;0 or x&lt;0 (strict inequality)
	 * @return simplified version of the inequality or <code>null</code> if no
	 *         simplification was possible
	 */
	private BooleanExpression simplifyIneq0(Monic monic, boolean gt,
			boolean strict) {
		SymbolicType type = monic.type();
		BooleanExpression result = null;
		BoundType boundType = getBoundTypeMonic(monic);

		if (boundType != null) {
			result = ineqFromBoundType(monic, boundType, gt, strict);
			return result;
		}
		if (monic instanceof Polynomial)
			return simplifyIneq0Poly((Polynomial) monic, gt, strict);
		if (monic instanceof Primitive)
			return null;

		// look for bounds on the primitive factors...
		PrimitivePower[] factorMap = monic.monicFactors(info.idealFactory);
		int numFactors = factorMap.length;
		boolean[] mask = new boolean[numFactors]; // unconstrained primitives
		List<Primitive> zeroList = new LinkedList<>();
		boolean positive = gt;
		int count = 0, unconstrained = 0;

		for (PrimitivePower pp : factorMap) {
			Primitive p = pp.primitive(info.idealFactory);
			BoundType primitiveBoundType = getBoundTypeMonic(p);

			if (primitiveBoundType == null) {
				mask[count] = true;
				unconstrained++;
			} else {
				switch (primitiveBoundType) {
				case ALL:
					mask[count] = true;
					unconstrained++;
					break;
				case EMPTY:
					// this means there is an inconsistency. this should have
					// been dealt with immediately when the inconsistency was
					// found
					throw new SARLInternalException(
							"unreachable: inconsistent primitive: " + p);
				case EQ0:
					// if one factor is 0, the whole product is 0
					return strict ? info.falseExpr : info.trueExpr;
				case GE0:
					// assume x>=0.
					// xy>=0 <=> x=0 || y>=0.
					// xy>0 <=> x!=0 && y>0.
					// xy<=0 <=> x=0 || y<=0.
					// xy<0 <=> x!=0 && y<0.
					zeroList.add(p);
					break;
				case GT0:
					// assume x>0.
					// xy>=0 <=> y>=0.
					// xy>0 <=> y>0.
					// xy<=0 <=> y<=0.
					// xy<0 <=> y<0.
					break;
				case LE0:
					// assume x<=0.
					// xy>=0 <=> x=0 || y<=0.
					// xy>0 <=> x!=0 && y<0.
					// xy<=0 <=> x=0 || y>=0.
					// xy<0 <=> x!=0 && y>0.
					zeroList.add(p);
					positive = !positive;
					break;
				case LT0:
					positive = !positive;
					break;
				default:
					throw new SARLInternalException("unreachable");
				}
			}
			count++;
		}
		if (numFactors == unconstrained)
			// everything unconstrained; no simplification possible
			return null;

		BooleanExpressionFactory bf = info.booleanFactory;
		Monomial zero = info.idealFactory.zero(type);

		if (unconstrained > 0) {
			// create new Monic from the unconstrained primitives
			Monic newMonic = info.idealFactory.monicMask(monic, mask);
			SymbolicOperator op = strict ? LESS_THAN : LESS_THAN_EQUALS;

			result = positive ? bf.booleanExpression(op, zero, newMonic)
					: bf.booleanExpression(op, newMonic, zero);
		} else { // newMonic is essentially 1
			result = positive ? info.trueExpr : info.falseExpr;
		}
		// if strict: conjunction (&&) with !=0 from zeroList
		// if !strict: disjunction(||) with ==0 from zeroList
		if (strict) {
			for (Primitive p : zeroList)
				result = bf.and(result, bf.booleanExpression(NEQ, zero, p));
		} else {
			for (Primitive p : zeroList)
				result = bf.or(result, bf.booleanExpression(EQUALS, zero, p));
		}
		return result;
	}

	/**
	 * <p>
	 * Simplifies expression poly OP 0, where poly is a {@link Polynomial} and
	 * OP is one of LT, LE, GT, or GE.
	 * </p>
	 * 
	 * Preconditions:
	 * <ul>
	 * <li>there is no entry in the {@link #constantMap} for <code>poly</code>
	 * </li>
	 * <li><code>poly</code> is fully expanded</li>
	 * <li><code>poly</code> has at least 2 terms</li>
	 * </ul>
	 * 
	 * @param poly
	 *            a {@link Polynomial} with at least 2 terms
	 * @param gt
	 *            is the condition one of <code>poly</code>&gt;0 or
	 *            <code>poly</code>&ge;0 ?
	 * @param strict
	 *            is the inequality strict, i.e., is the condition one of
	 *            <code>poly</code>&gt;0 or <code>poly</code>&lt;0 ?
	 * @return <code>null</code> if there is no way to express the constraint
	 *         beyond the obvious, else an expression equivalent to
	 *         <code>poly</code> OP 0, where the OP is the inequality operator
	 *         specified by <code>gt</code> and <code>strict</code>
	 */
	private BooleanExpression simplifyIneq0Poly(Polynomial poly, boolean gt,
			boolean strict) {
		AffineExpression affine = info.affineFactory.affine(poly);
		Monic pseudo = affine.pseudo(); // non-null since zep non-constant
		Number pseudoValue = constantMap.get(pseudo);
		AffineFactory af = info.affineFactory;

		if (pseudoValue != null) {
			// substitute known constant value for pseudo...
			Number val = af.affineValue(affine, pseudoValue);
			int sgn = val.signum();
			BooleanExpression result;

			if (gt) {
				result = (strict ? sgn > 0 : sgn >= 0) ? info.trueExpr
						: info.falseExpr;
			} else {
				result = (strict ? sgn < 0 : sgn <= 0) ? info.trueExpr
						: info.falseExpr;
			}
			return result;
		}

		Interval pseudoBound = boundMap.get(pseudo);

		if (pseudoBound == null)
			return null;

		// the following is a bound on poly
		Interval polyBound = info.numberFactory.affineTransform(pseudoBound,
				affine.coefficient(), affine.offset());
		BoundType boundType = boundType(polyBound);
		BooleanExpression result = ineqFromBoundType(poly, boundType, gt,
				strict);

		return result;
	}

	/**
	 * <p>
	 * Tries to compute a simplified version of the expression
	 * <code>primitive</code>=0. Returns <code>null</code> if no simplification
	 * is possible, else returns a {@link BooleanExpression} equivalent to
	 * <code>primitive</code>=0.
	 * </p>
	 * 
	 * <p>
	 * Precondition: primitive has been simplified
	 * </p>
	 * 
	 * @param primitive
	 *            a non-<code>null</code>, non-constant {@link Primitive}
	 * @return <code>null</code> or a {@link BooleanExpression} equivalent to
	 *         <code>primitive</code>=0
	 */
	private BooleanExpression simplifyEQ0(Primitive primitive) {
		Interval interval = boundMap.get(primitive);

		if (interval != null) {
			Number lo = interval.lower();

			if (lo != null) {
				int los = lo.signum();

				if (los > 0 || (los == 0 && interval.strictLower()))
					return info.falseExpr;
			}

			Number hi = interval.upper();

			if (hi != null) {
				int his = hi.signum();

				if (his < 0 || (his == 0 && interval.strictUpper()))
					return info.falseExpr;
			}
		}
		if (primitive instanceof Polynomial)
			return simplifyEQ0Poly((Polynomial) primitive);
		return null;
	}

	/**
	 * <p>
	 * Tries to compute a simplified version of the expression <code>poly</code>
	 * =0. Returns <code>null</code> if no simplification is possible, else
	 * returns a {@link BooleanExpression} equivalent to <code>poly</code>=0.
	 * </p>
	 * 
	 * <p>
	 * Pre-condition: <code>poly</code> has already gone through generic
	 * simplification and the method {@link #simplifiedEQ0Monic(Monic)}. So
	 * there is no need to look in the {@link #constantMap} or {@link #boundMap}
	 * for <code>poly</code>.
	 * </p>
	 * 
	 * @param primitive
	 *            a non-<code>null</code>, non-constant {@link Polynomial}
	 * @return <code>null</code> or a {@link BooleanExpression} equivalent to
	 *         <code>poly</code>=0
	 */
	private BooleanExpression simplifyEQ0Poly(Polynomial poly) {
		IdealFactory id = info.idealFactory;
		SymbolicType type = poly.type();
		AffineExpression affine = info.affineFactory.affine(poly);
		Monic pseudo = affine.pseudo(); // non-null since zep non-constant

		// if pseudo==poly, you have already tried looking it up
		// in the bound map in the monic method
		if (pseudo != poly) {
			// aX+b=0 => -b/a=X is an integer
			if (type.isInteger() && !info.numberFactory
					.mod((IntegerNumber) affine.offset(),
							(IntegerNumber) info.numberFactory
									.abs((IntegerNumber) affine.coefficient()))
					.isZero())
				return info.falseExpr;

			Interval interval = boundMap.get(pseudo);

			if (interval == null)
				return null;

			Number pseudoValue = info.numberFactory.negate(info.numberFactory
					.divide(affine.offset(), affine.coefficient()));

			// Know: lower <? pseudoValue <? upper
			// (Here "<?" means "<" or "<=".). So
			// lower - pseudoValue <? 0
			// upper - pseudoValue >? 0
			// if either of these is not true, you have a contradiction,
			// simplify to "false".
			// leftSign = sign of (lower-pseudoValue)
			// rightSign = sign of (upper-pseudoValue)

			Number lower = interval.lower();
			int leftSign = lower == null ? -1
					: info.numberFactory.subtract(lower, pseudoValue).signum();

			// if 0 is not in that interval, return FALSE
			if (leftSign > 0 || (leftSign == 0 && interval.strictLower()))
				return info.falseExpr;

			Number upper = interval.upper();
			int rightSign = upper == null ? 1
					: info.numberFactory.subtract(upper, pseudoValue).signum();

			if (rightSign < 0 || (rightSign == 0 && interval.strictUpper()))
				return info.falseExpr;
		}
		if (poly.hasNontrivialExpansion(id)) {
			Monomial[] termMap = poly.expand(id);

			if (termMap.length == 0)
				return info.trueExpr;

			Monomial newMonomial = id.factorTermMap(termMap);
			BooleanExpression newExpression = id.isZero(newMonomial);
			BooleanExpression result = (BooleanExpression) apply(newExpression);

			if (result != poly)
				return result;
		}
		return null;
	}

	private RationalExpression simplifyRationalExpression(
			RationalExpression expression) {
		if (expression instanceof Constant)
			return expression;

		RationalExpression result1;

		if (expression instanceof Polynomial)
			result1 = simplifyPolynomial((Polynomial) expression);
		else if (expression instanceof Monic)
			result1 = simplifyMonic((Monic) expression);
		else
			result1 = (RationalExpression) simplifyGenericExpression(
					expression);
		if (result1 instanceof Primitive || result1 instanceof Constant)
			return result1;

		RationalExpression result2 = simplifyPowersRational(result1);

		if (result1 == result2)
			return result1;
		return (RationalExpression) apply(result2);
	}

	// Exported methods.............................................

	/**
	 * {@inheritDoc}
	 * 
	 * <p>
	 * Simplifies an expression, providing special handling beyond the generic
	 * simplification for ideal expressions. Relational expressions also get
	 * special handling. All other expressions are simplified generically.
	 * </p>
	 * 
	 * <p>
	 * This method does not look in the simplify cache for an existing
	 * simplification of expression. See the documentation for the super method.
	 * </p>
	 * 
	 * @see {@link #simplifyGenericExpression}
	 * @see {@link #simplifyRelational}
	 * @see {@link #simplifyPolynomial}
	 */
	@Override
	protected SymbolicExpression simplifyExpression(
			SymbolicExpression expression) {
		if (expression instanceof RationalExpression)
			return simplifyRationalExpression((RationalExpression) expression);

		SymbolicType type = expression.type();

		if (type != null) {
			if (type.isBoolean()) {
				if (expression.isTrue() || expression.isFalse())
					return expression;

				Boolean booleanResult = booleanMap.get(expression);

				if (booleanResult != null) {
					SymbolicExpression result = booleanResult ? info.trueExpr
							: info.falseExpr;

					if (debugSimps) {
						out.println("Simplifier boolean :" + expression);
						out.println("Simplifier result  :" + result);
					}
					return result;
				}
				if (isNumericRelational(expression))
					return simplifyRelational((BooleanExpression) expression);
			} else if (!type.isNumeric()) {
				SymbolicExpression constant = otherConstantMap.get(expression);

				if (constant != null) {
					if (debugSimps) {
						out.println("Simplify constant expr   : " + expression);
						out.println("Simplifiy constant result: " + constant);
					}
					return constant;
				}
			}
		}
		return simplifyGenericExpression(expression);
	}

	@Override
	public Interval assumptionAsInterval(SymbolicConstant symbolicConstant) {
		if (intervalComputed) {
			if (theInterval != null
					&& intervalVariable.equals(symbolicConstant))
				return theInterval;
			return null;
		}
		intervalComputed = true;
		if (!booleanMap.isEmpty() || !rawAssumption.isTrue()) {
			return null;
		}
		if (!constantMap.isEmpty()) {
			if (!boundMap.isEmpty() || constantMap.size() != 1) {
				return null;
			}
			Entry<Monic, Number> entry = constantMap.entrySet().iterator()
					.next();
			Monic fp1 = entry.getKey();
			Number value = entry.getValue();

			if (!fp1.equals(symbolicConstant)) {
				return null;
			}
			theInterval = info.numberFactory.singletonInterval(value);
			intervalVariable = symbolicConstant;
			return theInterval;
		}
		if (boundMap.size() == 1) {
			Entry<Monic, Interval> entry = boundMap.entrySet().iterator()
					.next();
			Monic fp1 = entry.getKey();

			if (!fp1.equals(symbolicConstant)) {
				return null;
			}
			theInterval = entry.getValue();
			intervalVariable = symbolicConstant;
			return theInterval;
		}
		return null;
	}

	@Override
	public Map<SymbolicConstant, SymbolicExpression> substitutionMap() {
		if (substitutionMap == null) {
			substitutionMap = new HashMap<SymbolicConstant, SymbolicExpression>();
			for (Entry<Monic, Number> entry : constantMap.entrySet()) {
				Monic fp = entry.getKey();

				if (fp instanceof SymbolicConstant)
					substitutionMap.put((SymbolicConstant) fp,
							universe.number(entry.getValue()));
			}
			for (Entry<SymbolicExpression, SymbolicExpression> entry : otherConstantMap
					.entrySet()) {
				SymbolicExpression expr = entry.getKey();

				if (expr instanceof SymbolicConstant)
					substitutionMap.put((SymbolicConstant) expr,
							entry.getValue());
			}
			for (Entry<BooleanExpression, Boolean> entry : booleanMap
					.entrySet()) {
				BooleanExpression primitive = entry.getKey();

				if (primitive instanceof SymbolicConstant)
					substitutionMap.put((SymbolicConstant) primitive,
							universe.bool(entry.getValue()));
			}
		}
		return substitutionMap;
	}

	@Override
	public BooleanExpression getReducedContext() {
		return assumption;
	}

	@Override
	public BooleanExpression getFullContext() {
		if (fullContext == null) {
			Map<SymbolicConstant, SymbolicExpression> map = substitutionMap();

			fullContext = getReducedContext();
			for (Entry<SymbolicConstant, SymbolicExpression> entry : map
					.entrySet()) {
				SymbolicConstant key = entry.getKey();
				SymbolicExpression value = entry.getValue();
				BooleanExpression equation = universe.equals(key, value);

				fullContext = universe.and(fullContext, equation);
			}
		}
		return fullContext;
	}
}
