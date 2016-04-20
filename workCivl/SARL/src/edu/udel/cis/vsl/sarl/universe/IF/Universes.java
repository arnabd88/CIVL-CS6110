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
package edu.udel.cis.vsl.sarl.universe.IF;

import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.config.Configurations;
import edu.udel.cis.vsl.sarl.IF.config.ProverInfo;
import edu.udel.cis.vsl.sarl.IF.config.SARLConfig;
import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.expr.IF.ExpressionFactory;
import edu.udel.cis.vsl.sarl.expr.IF.Expressions;
import edu.udel.cis.vsl.sarl.ideal.IF.Ideal;
import edu.udel.cis.vsl.sarl.ideal.IF.IdealFactory;
import edu.udel.cis.vsl.sarl.number.IF.Numbers;
import edu.udel.cis.vsl.sarl.object.IF.ObjectFactory;
import edu.udel.cis.vsl.sarl.object.IF.Objects;
import edu.udel.cis.vsl.sarl.preuniverse.IF.FactorySystem;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverses;
import edu.udel.cis.vsl.sarl.prove.IF.Prove;
import edu.udel.cis.vsl.sarl.prove.IF.TheoremProverFactory;
import edu.udel.cis.vsl.sarl.reason.IF.Reason;
import edu.udel.cis.vsl.sarl.reason.IF.ReasonerFactory;
import edu.udel.cis.vsl.sarl.simplify.IF.SimplifierFactory;
import edu.udel.cis.vsl.sarl.simplify.IF.Simplify;
import edu.udel.cis.vsl.sarl.type.IF.SymbolicTypeFactory;
import edu.udel.cis.vsl.sarl.type.IF.Types;
import edu.udel.cis.vsl.sarl.universe.common.CommonSymbolicUniverse;
import edu.udel.cis.vsl.sarl.universe.common.MathUniverse;

/**
 * This class provides static methods for the creation of new
 * {@link SymbolicUniverse}s.
 * 
 * @author siegel
 */
public class Universes {

	public static SymbolicUniverse newIdealUniverse2(SARLConfig config,
			ProverInfo prover) {
		FactorySystem system = PreUniverses.newIdealFactorySystem2();
		CommonSymbolicUniverse universe = new CommonSymbolicUniverse(system);
		SimplifierFactory simplifierFactory = Ideal.newIdealSimplifierFactory(
				(IdealFactory) system.numericFactory(), universe);
		TheoremProverFactory proverFactory = prover == null
				? Prove.newMultiProverFactory(universe, config)
				: Prove.newProverFactory(universe, prover);
		ReasonerFactory reasonerFactory = Reason.newReasonerFactory(universe,
				simplifierFactory, proverFactory);

		universe.setReasonerFactory(reasonerFactory);
		return universe;
	}

	public static SymbolicUniverse newIdealUniverse2() {
		return newIdealUniverse2(Configurations.getDefaultConfiguration(),
				null);
	}

	public static SymbolicUniverse newMathUniverse(SARLConfig config,
			ProverInfo prover) {
		FactorySystem system = PreUniverses.newIdealFactorySystem2();
		MathUniverse universe = new MathUniverse(system);
		SimplifierFactory simplifierFactory = Ideal.newIdealSimplifierFactory(
				(IdealFactory) system.numericFactory(), universe);
		TheoremProverFactory proverFactory = prover == null
				? Prove.newMultiProverFactory(universe, config)
				: Prove.newProverFactory(universe, prover);
		ReasonerFactory reasonerFactory = Reason.newReasonerFactory(universe,
				simplifierFactory, proverFactory);

		universe.setReasonerFactory(reasonerFactory);
		return universe;
	}

	public static SymbolicUniverse newMathUniverse() {
		return newMathUniverse(Configurations.getDefaultConfiguration(), null);
	}

	public static SymbolicUniverse newHerbrandUniverse(SARLConfig config,
			ProverInfo prover) {
		FactorySystem system = PreUniverses.newHerbrandFactorySystem();
		CommonSymbolicUniverse universe = new CommonSymbolicUniverse(system);
		SimplifierFactory simplifierFactory = Simplify
				.newIdentitySimplifierFactory(universe);
		TheoremProverFactory proverFactory = prover == null
				? Prove.newMultiProverFactory(universe, config)
				: Prove.newProverFactory(universe, prover);
		ReasonerFactory reasonerFactory = Reason.newReasonerFactory(universe,
				simplifierFactory, proverFactory);

		universe.setReasonerFactory(reasonerFactory);
		return universe;
	}

	public static SymbolicUniverse newHerbrandUniverse() {
		return newHerbrandUniverse(Configurations.getDefaultConfiguration(),
				null);
	}

	public static SymbolicUniverse newStandardUniverse2(SARLConfig config,
			ProverInfo prover) {
		NumberFactory numberFactory = Numbers.REAL_FACTORY;
		ObjectFactory objectFactory = Objects.newObjectFactory(numberFactory);
		SymbolicTypeFactory typeFactory = Types.newTypeFactory(objectFactory);
		ExpressionFactory expressionFactory = Expressions
				.newStandardExpressionFactory2(numberFactory, objectFactory,
						typeFactory);
		FactorySystem system = PreUniverses.newFactorySystem(objectFactory,
				typeFactory, expressionFactory);
		CommonSymbolicUniverse universe = new CommonSymbolicUniverse(system);
		SimplifierFactory simplifierFactory = Expressions
				.standardSimplifierFactory2(expressionFactory, universe);
		TheoremProverFactory proverFactory = prover == null
				? Prove.newMultiProverFactory(universe, config)
				: Prove.newProverFactory(universe, prover);
		ReasonerFactory reasonerFactory = Reason.newReasonerFactory(universe,
				simplifierFactory, proverFactory);

		universe.setReasonerFactory(reasonerFactory);
		return universe;
	}

	public static SymbolicUniverse newStandardUniverse2() {
		return newStandardUniverse2(Configurations.getDefaultConfiguration(),
				null);
	}

	// public static TrigonometricUniverse newTrigonometricUniverse() {
	// NumberFactory numberFactory = Numbers.REAL_FACTORY;
	// ObjectFactory objectFactory = Objects.newObjectFactory(numberFactory);
	// SymbolicTypeFactory typeFactory = Types.newTypeFactory(objectFactory);
	// CollectionFactory collectionFactory = Collections
	// .newCollectionFactory(objectFactory);
	// ExpressionFactory expressionFactory = Expressions
	// .newStandardExpressionFactory(numberFactory, objectFactory,
	// typeFactory, collectionFactory);
	// FactorySystem system = PreUniverses.newFactorySystem(objectFactory,
	// typeFactory, expressionFactory, collectionFactory);
	// TrigonometricUniverse universe = new TrigonometricUniverse(system);
	// SimplifierFactory simplifierFactory = Expressions
	// .standardSimplifierFactory(expressionFactory, universe);
	// TheoremProverFactory proverFactory = Prove
	// .newCVC3TheoremProverFactory(universe);
	// ReasonerFactory reasonerFactory = Reason.newReasonerFactory(
	// simplifierFactory, proverFactory);
	//
	// universe.setReasonerFactory(reasonerFactory);
	// return universe;
	// }

}
