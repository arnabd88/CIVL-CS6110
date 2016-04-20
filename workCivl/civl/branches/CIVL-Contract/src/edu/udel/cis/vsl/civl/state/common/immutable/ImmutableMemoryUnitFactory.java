package edu.udel.cis.vsl.civl.state.common.immutable;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.state.IF.MemoryUnit;
import edu.udel.cis.vsl.civl.state.IF.MemoryUnitFactory;
import edu.udel.cis.vsl.civl.state.IF.MemoryUnitSet;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NTReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;

public class ImmutableMemoryUnitFactory implements MemoryUnitFactory {
	/**
	 * The map of canonic memory unit sets. The key and the corresponding value
	 * should be the same, in order to allow fast checking of existence and
	 * returning the value.
	 */
	private Map<ImmutableMemoryUnitSet, ImmutableMemoryUnitSet> muSetMap = new HashMap<>(
			100000);
	/**
	 * The map of canonic memory unit. The key and the corresponding value
	 * should be the same, in order to allow fast checking of existence and
	 * returning the value.
	 */
	private Map<ImmutableMemoryUnit, ImmutableMemoryUnit> muMap = new HashMap<>(
			100000);

	private ModelFactory modelFactory;

	/**
	 * The symbolic universe, provided by SARL.
	 */
	private SymbolicUniverse universe;

	private IntObject zero;
	private IntObject one;
	private IntObject two;

	public ImmutableMemoryUnitFactory(SymbolicUniverse universe,
			ModelFactory factory) {
		this.universe = universe;
		this.zero = universe.intObject(0);
		this.one = universe.intObject(1);
		this.two = universe.intObject(2);
		this.modelFactory = factory;
	}

	@Override
	public ImmutableMemoryUnitSet canonic(MemoryUnitSet muSet) {
		ImmutableMemoryUnitSet theSet = (ImmutableMemoryUnitSet) muSet;

		if (theSet.isCanonic())
			return theSet;
		else {
			ImmutableMemoryUnitSet result = muSetMap.get(theSet);

			if (result == null) {
				result = theSet;
				result.makeCanonic(universe, muMap);
				muSetMap.put(result, result);
			}
			return result;
		}
	}

	@Override
	public boolean isJoint(MemoryUnit mu1, MemoryUnit mu2) {
		if (mu1.dyscopeID() != mu2.dyscopeID())
			return false;
		if (mu1.varID() != mu2.varID())
			return false;
		return this.isJoint(mu1.reference(), mu2.reference());
	}

	@Override
	public boolean isJoint(MemoryUnitSet muSet, MemoryUnit mu) {
		for (MemoryUnit memUnit : muSet.memoryUnits())
			if (isJoint(memUnit, mu))
				return true;
		return false;
	}

	@Override
	public ImmutableMemoryUnitSet union(MemoryUnitSet muSet1,
			MemoryUnitSet muSet2) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public ImmutableMemoryUnitSet intersects(MemoryUnitSet muSet1,
			MemoryUnitSet muSet2) {
		// TODO Auto-generated method stub
		return null;
	}

	// private ReferenceExpression leastCommonAncestor(ReferenceExpression ref1,
	// ReferenceExpression ref2) {
	// // TODO
	// return null;
	// }

	/**
	 * Are the two given references disjoint?
	 * 
	 * @param ref1
	 *            The first reference expression.
	 * @param ref2
	 *            The second reference expression.
	 * @return True iff the two given references do NOT have any intersection.
	 */
	private boolean isJoint(ReferenceExpression ref1, ReferenceExpression ref2) {
		List<ReferenceExpression> ancestors1, ancestors2;
		int numAncestors1, numAncestors2, minNum;

		if (ref1.isIdentityReference() || ref2.isIdentityReference())
			return true;
		ancestors1 = this.ancestorsOfRef(ref1);
		ancestors2 = this.ancestorsOfRef(ref2);
		numAncestors1 = ancestors1.size();
		numAncestors2 = ancestors2.size();
		minNum = numAncestors1 <= numAncestors2 ? numAncestors1 : numAncestors2;
		for (int i = 0; i < minNum; i++) {
			ReferenceExpression ancestor1 = ancestors1.get(i), ancestor2 = ancestors2
					.get(i);
			BooleanExpression sameAncestors = universe.equals(ancestor1,
					ancestor2);

			if (!sameAncestors.isFalse())
				return true;
		}
		return false;
	}

	private List<ReferenceExpression> ancestorsOfRef(ReferenceExpression ref) {
		if (ref.isIdentityReference())
			return new ArrayList<>();
		else {
			List<ReferenceExpression> result;

			result = ancestorsOfRef(((NTReferenceExpression) ref).getParent());
			result.add(ref);
			return result;
		}
	}

	@Override
	public void add(MemoryUnitSet muSet, MemoryUnit mu) {
		// if (!this.isJoint(muSet, mu))
		muSet.add(mu);
	}

	@Override
	public void add(MemoryUnitSet muSet, SymbolicExpression pointer) {
		int scope = modelFactory.getScopeId(null,
				universe.tupleRead(pointer, zero));
		int var = ((IntegerNumber) universe
				.extractNumber((NumericExpression) universe.tupleRead(pointer,
						one))).intValue();
		ReferenceExpression reference = (ReferenceExpression) universe
				.tupleRead(pointer, two);
		ImmutableMemoryUnit mu = this.newMemoryUnit(scope, var, reference);

		this.add(muSet, mu);
	}

	@Override
	public ImmutableMemoryUnit newMemoryUnit(int dyscopeID, int varID,
			ReferenceExpression reference) {
		return new ImmutableMemoryUnit(dyscopeID, varID, reference);
	}

	@Override
	public ImmutableMemoryUnitSet newMemoryUnitSet() {
		return new ImmutableMemoryUnitSet();
	}

	@Override
	public boolean isJoint(MemoryUnitSet muSet1, MemoryUnitSet muSet2) {
		for (MemoryUnit mu1 : muSet1.memoryUnits())
			if (this.isJoint(muSet2, mu1))
				return true;
		return false;
	}
}
