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

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.IF.number.RationalNumber;
import edu.udel.cis.vsl.sarl.ideal.IF.IdealFactory;
import edu.udel.cis.vsl.sarl.ideal.IF.Monic;
import edu.udel.cis.vsl.sarl.ideal.IF.Monomial;
import edu.udel.cis.vsl.sarl.ideal.IF.Polynomial;

/**
 * <p>
 * Simplifies a constant map. This take as input a map which associates constant
 * values to {@link Monic}s. Some of these monics may be instances of
 * {@link Polynomial}, in which case they will be in pseudo-primitive form: no
 * constant term, leading coefficient is positive, leading coefficient is 1 (for
 * real type), or GCD of absolute value of coefficients is 1 (for integer type).
 * We will use the word "polynomial" to refer to all entries in the map, whether
 * or not they are instances of {@link Polynomial}. The {@link Monic}s which are
 * not instances of {@link Polynomial} may be considered a polynomial with one
 * term which has a coefficient of 1.
 * </p>
 * 
 * <p>
 * It simplifies this map by performing Gaussian elimination (aka, Gauss-Jordan
 * elimination) on the coefficient matrix formed by the terms, i.e., the
 * "variables" are considered to be the {@link Monic}s which occur in the terms
 * and the "coefficients" are the monomial coefficients of those {@link Monic}s.
 * </p>
 * 
 * <p>
 * Specifically, it separates out the integer and the real entries and works on
 * each separately. In each case, it constructs a matrix in which the rows
 * correspond to map entries and columns correspond to the monics of the terms
 * (of the appropriate type) which occur anywhere in the map. The entry in a
 * column is the coefficient of that monic in the polynomial which occurs as the
 * key in the map entry. It then performs Gaussian elimination on these matrices
 * to reduce to reduced row echelon form. It then re-constructs the maps in this
 * reduced form.
 * </p>
 * 
 * <p>
 * There is an extra column on the right of the matrix for the constant
 * associated to the polynomial.
 * </p>
 * 
 * <p>
 * If an inconsistency exists ( for example, X+Y maps to 0, X maps to 0, Y maps
 * to 1) in the map, this will be discovered in the elimination. In this case,
 * the boolean value false is returned by method reduce. True is returned if
 * there are no problems.
 * </p>
 */
public class LinearSolver {

	private NumberFactory numberFactory;

	private IdealFactory idealFactory;

	private RationalNumber[][] intMatrix, realMatrix;

	private int numIntConstraints = 0, numRealConstraints = 0;

	private Set<Monic> intMonicSet = new HashSet<Monic>();

	private Set<Monic> realMonicSet = new HashSet<Monic>();

	// this has to change. the map now maps Monic to Numbers.
	// Some of those Monics may be Polynomials...

	private Map<Monic, Number> map;

	private Monic[] intMonics, realMonics;

	private Map<Monic, Integer> intIdMap, realIdMap;

	LinearSolver(IdealFactory idealFactory) {
		this.idealFactory = idealFactory;
		this.numberFactory = idealFactory.numberFactory();
	}

	/**
	 * Extracts the monics that are used in the map and initializes data
	 * structures. The following are initialized: intMonicSec, realMonicSet,
	 * intMonics, realMonics, intIdMap, realIdMap.
	 */
	private void extractMonics() {
		int numIntMonics, numRealMonics, i;

		for (Monic key : map.keySet()) {
			Set<Monic> monics;

			if (key.type().isInteger()) {
				numIntConstraints++;
				monics = intMonicSet;

			} else {
				numRealConstraints++;
				monics = realMonicSet;
			}
			for (Monomial term : key.termMap(idealFactory)) {
				Monic monic = term.monic(idealFactory);

				// polynomials should not have constant term:
				assert !monic.isOne();
				monics.add(monic);
			}
		}
		numIntMonics = intMonicSet.size();
		numRealMonics = realMonicSet.size();
		intMonics = new Monic[numIntMonics];
		realMonics = new Monic[numRealMonics];
		intIdMap = new HashMap<Monic, Integer>(numIntMonics);
		realIdMap = new HashMap<Monic, Integer>(numRealMonics);

		i = 0;
		for (Monic monic : intMonicSet)
			intMonics[i++] = monic;
		i = 0;
		for (Monic monic : realMonicSet)
			realMonics[i++] = monic;
		Arrays.sort(intMonics, idealFactory.monicComparator());
		Arrays.sort(realMonics, idealFactory.monicComparator());
		for (i = 0; i < numIntMonics; i++)
			intIdMap.put(intMonics[i], i);
		for (i = 0; i < numRealMonics; i++)
			realIdMap.put(realMonics[i], i);
	}

	/**
	 * Builds the matrix representations of the maps. For the integer
	 * constraints, there is one row for each integer entry in the map and one
	 * column for each monic of integer type, plus one additional column to hold
	 * the value associated to the constant value associated to the map entry.
	 * The real map is similar.
	 */
	private void buildMatrices() {
		int numIntMonics = intMonics.length;
		int numRealMonics = realMonics.length;
		int intConstraintId = 0, realConstraintId = 0;

		intMatrix = new RationalNumber[numIntConstraints][numIntMonics + 1];
		realMatrix = new RationalNumber[numRealConstraints][numRealMonics + 1];
		for (int i = 0; i < numIntConstraints; i++)
			for (int j = 0; j < numIntMonics; j++)
				intMatrix[i][j] = numberFactory.zeroRational();
		for (int i = 0; i < numRealConstraints; i++)
			for (int j = 0; j < numRealMonics; j++)
				realMatrix[i][j] = numberFactory.zeroRational();
		for (Entry<Monic, Number> entry : map.entrySet()) {
			Monic key = entry.getKey();
			Number value = entry.getValue();

			if (key.type().isInteger()) {
				intMatrix[intConstraintId][numIntMonics] = numberFactory
						.rational(value);
				for (Monomial term : key.termMap(idealFactory)) {
					Monic monic = term.monic(idealFactory);
					Number coefficient = term.monomialConstant(idealFactory)
							.number();

					intMatrix[intConstraintId][intIdMap
							.get(monic)] = numberFactory.rational(coefficient);
				}
				intConstraintId++;
			} else {
				realMatrix[realConstraintId][numRealMonics] = (RationalNumber) value;

				for (Monomial term : key.termMap(idealFactory)) {
					Monic monic = term.monic(idealFactory);
					Number coefficient = term.monomialConstant(idealFactory)
							.number();

					realMatrix[realConstraintId][realIdMap
							.get(monic)] = (RationalNumber) coefficient;
				}
				realConstraintId++;
			}
		}
	}

	private boolean rebuildIntMap() {
		int numIntMonics = intMonics.length;

		for (int i = 0; i < numIntConstraints; i++) {
			Monomial poly = idealFactory.zeroInt();
			IntegerNumber lcm = numberFactory.oneInteger();

			// clear the denominators in row i by multiplying
			// every entry in the row by the LCM
			for (int j = 0; j <= numIntMonics; j++) {
				RationalNumber a = intMatrix[i][j];

				if (!a.isZero()) {
					IntegerNumber denominator = numberFactory.denominator(a);

					if (!denominator.isOne())
						lcm = numberFactory.lcm(lcm, denominator);
				}
			}
			for (int j = 0; j < numIntMonics; j++) {
				RationalNumber a = intMatrix[i][j];

				if (!a.isZero()) {
					IntegerNumber coefficient = numberFactory
							.multiply(numberFactory.numerator(a), numberFactory
									.divide(lcm, numberFactory.denominator(a)));

					poly = idealFactory.addMonomials(poly,
							idealFactory.monomial(
									idealFactory.constant(coefficient),
									intMonics[j]));
				}
			}

			IntegerNumber value = numberFactory.multiply(
					numberFactory.numerator(intMatrix[i][numIntMonics]),
					numberFactory.divide(lcm, numberFactory
							.denominator(intMatrix[i][numIntMonics])));

			if (poly.isZero()) {
				if (!value.isZero()) { // inconsistency
					return false;
				}
			} else {
				Monic key;

				if (poly instanceof Monic) {
					key = (Monic) poly;
				} else {
					IntegerNumber c = (IntegerNumber) poly
							.monomialConstant(idealFactory).number();

					if (!numberFactory
							.mod((IntegerNumber) numberFactory.abs(value),
									(IntegerNumber) numberFactory.abs(c))
							.isZero()) {
						return false; // inconsistency
					}
					key = poly.monic(idealFactory);
					value = numberFactory.divide(value, c);
				}
				map.put(key, value);
			}
		}
		return true;
	}

	private boolean rebuildRealMap() {
		int numRealMonics = realMonics.length;

		for (int i = 0; i < numRealConstraints; i++) {
			Monomial poly = idealFactory.zeroReal();
			RationalNumber value = realMatrix[i][numRealMonics];

			for (int j = 0; j < numRealMonics; j++) {
				RationalNumber a = realMatrix[i][j];

				if (a.signum() != 0) {
					poly = idealFactory.addMonomials(poly, idealFactory
							.monomial(idealFactory.constant(a), realMonics[j]));
				}
			}
			if (poly.isZero()) {
				if (!value.isZero()) { // inconsistency
					return false;
				}
			} else {
				// leading coefficient is 1 because of reduced row-echelon form
				// there is no constant term, so poly is in pseudo-primitive
				// form
				Monic key;

				if (poly instanceof Monic) {
					key = (Monic) poly;
				} else {
					key = poly.monic(idealFactory);
					value = (RationalNumber) numberFactory.divide(value,
							poly.monomialConstant(idealFactory).number());
				}
				map.put(key, value);
			}
		}
		return true;
	}

	boolean reduce(Map<Monic, Number> map) {
		this.map = map;

		// Step 1: extract monics. Uses map. Yields intIdMap, realIdMap,
		// intMonics, realMonics.

		// Step 2: build matrices. Uses intIdMap, realIdMap, intMonics,
		// realMonics, map. Yields intMatrix[][], realMatrix[][].

		// Step 3. perform Gauss-Jordan elimination on matrices.

		// Step 4. re-build map. Uses map, intMonics, realMonics, intMatrix,
		// realMatrix. Modifies map.

		extractMonics();
		buildMatrices();
		map.clear();
		numberFactory.gaussianElimination(intMatrix);
		numberFactory.gaussianElimination(realMatrix);
		if (!rebuildIntMap())
			return false;
		if (!rebuildRealMap())
			return false;
		return true;
	}

	public static boolean reduceConstantMap(IdealFactory idealFactory,
			Map<Monic, Number> map) {
		LinearSolver solver = new LinearSolver(idealFactory);

		return solver.reduce(map);
	}
}
