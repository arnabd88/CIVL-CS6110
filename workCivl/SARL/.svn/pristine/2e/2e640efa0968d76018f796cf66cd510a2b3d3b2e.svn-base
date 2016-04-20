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
package edu.udel.cis.vsl.sarl.expr.IF;

import edu.udel.cis.vsl.sarl.IF.SARLInternalException;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.expr.cnf.CnfFactory;
import edu.udel.cis.vsl.sarl.expr.common.CommonExpressionFactory;
import edu.udel.cis.vsl.sarl.expr.common.CommonNumericExpressionFactory;
import edu.udel.cis.vsl.sarl.herbrand.IF.Herbrand;
import edu.udel.cis.vsl.sarl.ideal.IF.Ideal;
import edu.udel.cis.vsl.sarl.ideal.IF.IdealFactory;
import edu.udel.cis.vsl.sarl.object.IF.ObjectFactory;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;
import edu.udel.cis.vsl.sarl.simplify.IF.Simplifier;
import edu.udel.cis.vsl.sarl.simplify.IF.SimplifierFactory;
import edu.udel.cis.vsl.sarl.type.IF.SymbolicTypeFactory;

/**
 * This class provides static methods for producing factories that create
 * various kinds of {@link SymbolicExpression}.
 * 
 * @author siegel
 *
 */
public class Expressions {

	/**
	 * Produces a new instance of the standard expression factory.
	 * 
	 * @param numericFactory
	 *            the numeric factory that the new standard expression factory
	 *            will use for the creation of {@link NumericExpression}s.
	 * @return the new expression factory
	 */
	public static ExpressionFactory newExpressionFactory(
			NumericExpressionFactory numericFactory) {
		return new CommonExpressionFactory(numericFactory);
	}

	/**
	 * Produces a new factory for creating {@link BooleanExpression}s that uses
	 * Conjunctive Normal Form (CNF) as the canonical representation of boolean
	 * expressions.
	 * 
	 * @param typeFactory
	 *            the type factory that should be used by the new boolean
	 *            factory
	 * @param objectFactory
	 *            the object factory that should be used by the new boolean
	 *            factory
	 * @param collectionFactory
	 *            the collection factory that should be used by the new boolean
	 *            factory
	 * @return the new boolean expression factory
	 */
	public static BooleanExpressionFactory newCnfFactory(
			SymbolicTypeFactory typeFactory, ObjectFactory objectFactory) {
		return new CnfFactory(typeFactory, objectFactory);
	}

	/**
	 * Produces a new expression factory in which the underlying
	 * {@link NumericExpressionFactory} uses "ideal" (mathematical) integer and
	 * real arithmetic, i.e., infinite precision, unbounded arithmetic. The
	 * {@link BooleanExpressionFactory} will use the standard CNF form for
	 * boolean expressions.
	 * 
	 * @param numberFactory
	 *            the factory used to produce and manipulate concrete
	 *            {@link edu.udel.cis.vsl.sarl.IF.number.Number}s.
	 * @param objectFactory
	 *            factory used to produce {@link SymbolicObject}s
	 * @param typeFactory
	 *            factory used to produce {@link SymbolicType}s
	 * @param collectionFactory
	 *            factory used to produce {@link SymbolicCollection}s
	 * @return the new ideal expression factory
	 */
	public static ExpressionFactory newIdealExpressionFactory2(
			NumberFactory numberFactory, ObjectFactory objectFactory,
			SymbolicTypeFactory typeFactory) {
		BooleanExpressionFactory booleanFactory = new CnfFactory(typeFactory,
				objectFactory);
		NumericExpressionFactory numericFactory = Ideal.newIdealFactory(
				numberFactory, objectFactory, typeFactory, booleanFactory);

		return newExpressionFactory(numericFactory);
	}

	/**
	 * Produces a new expression factory in which the underlying
	 * {@link NumericExpressionFactory} is based on "Herbrand arithmetic", i.e.,
	 * arithmetic in which the numeric operations are treated as uninterpreted
	 * functions.
	 * 
	 * @param numberFactory
	 *            the factory used to produce and manipulate concrete
	 *            {@link edu.udel.cis.vsl.sarl.IF.number.Number}s.
	 * @param objectFactory
	 *            factory used to produce {@link SymbolicObject}s
	 * @param typeFactory
	 *            factory used to produce {@link SymbolicType}s
	 * @param collectionFactory
	 *            factory used to produce {@link SymbolicCollection}s
	 * @return the new Herbrand expression factory
	 */
	public static ExpressionFactory newHerbrandExpressionFactory(
			NumberFactory numberFactory, ObjectFactory objectFactory,
			SymbolicTypeFactory typeFactory) {
		BooleanExpressionFactory booleanFactory = new CnfFactory(typeFactory,
				objectFactory);
		NumericExpressionFactory numericFactory = Herbrand.newHerbrandFactory(
				numberFactory, objectFactory, typeFactory, booleanFactory);

		return newExpressionFactory(numericFactory);
	}

	/**
	 * Produces a new expression factory that uses both Herbrand and Ideal
	 * arithmetic. The choice of which kind of arithmetic to use is determined
	 * by the types of the arguments to the numerical operators.
	 * 
	 * @param numberFactory
	 *            the factory used to produce and manipulate concrete
	 *            {@link edu.udel.cis.vsl.sarl.IF.number.Number}s.
	 * @param objectFactory
	 *            factory used to produce {@link SymbolicObject}s
	 * @param typeFactory
	 *            factory used to produce {@link SymbolicType}s
	 * @param collectionFactory
	 *            factory used to produce {@link SymbolicCollection}s
	 * @return the new standard (Herbrand-Ideal composite) expression factory
	 */
	public static ExpressionFactory newStandardExpressionFactory2(
			NumberFactory numberFactory, ObjectFactory objectFactory,
			SymbolicTypeFactory typeFactory) {
		BooleanExpressionFactory booleanFactory = new CnfFactory(typeFactory,
				objectFactory);
		NumericExpressionFactory idealFactory = Ideal.newIdealFactory(
				numberFactory, objectFactory, typeFactory, booleanFactory);
		NumericExpressionFactory herbrandFactory = Herbrand.newHerbrandFactory(
				numberFactory, objectFactory, typeFactory, booleanFactory);
		NumericExpressionFactory numericFactory = new CommonNumericExpressionFactory(
				idealFactory, herbrandFactory);

		return newExpressionFactory(numericFactory);
	}

	/**
	 * Produces a new factory for creating {@link Simplifier}s for a standard
	 * expression factory.
	 * 
	 * @param standardExpressionFactory
	 *            a standard expression factory which uses Ideal and Herbrand
	 *            arithmetic
	 * @param universe
	 *            the pre-universe used to make symbolic expressions
	 * @return the new simplifier factory
	 */
	public static SimplifierFactory standardSimplifierFactory2(
			ExpressionFactory standardExpressionFactory, PreUniverse universe) {
		NumericExpressionFactory numericFactory = standardExpressionFactory
				.numericFactory();
		IdealFactory idealFactory;

		if (numericFactory instanceof IdealFactory)
			idealFactory = (IdealFactory) numericFactory;
		else if (numericFactory instanceof CommonNumericExpressionFactory)
			idealFactory = (IdealFactory) ((CommonNumericExpressionFactory) numericFactory)
					.idealFactory();
		else
			throw new SARLInternalException("Unknown expression factory kind.");

		return Ideal.newIdealSimplifierFactory(idealFactory, universe);
	}
}
