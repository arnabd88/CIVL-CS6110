package edu.udel.cis.vsl.civl.state.common.immutable;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.udel.cis.vsl.civl.state.IF.MemoryUnit;
import edu.udel.cis.vsl.civl.state.IF.MemoryUnitSet;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;

/**
 * TODO: think about a general way for canonicalization like a canonic
 * interface, a canonicalizer, etc.
 * 
 * @author zmanchun
 *
 */
public class ImmutableMemoryUnitSet implements MemoryUnitSet {

	private Set<MemoryUnit> memUnits;

	private boolean canonic;

	ImmutableMemoryUnitSet(ImmutableMemoryUnitSet muSet) {
		this.memUnits = new HashSet<>(muSet.memUnits);
	}

	ImmutableMemoryUnitSet() {
		this.memUnits = new HashSet<>();
	}

	/**
	 * Makes this ImmutableMemoryUnitSet canonic. Recursively makes all memory
	 * units contained in this set canonic.
	 * 
	 * @param canonicId
	 *            the canonic ID to assign to this state
	 * @param universe
	 *            the symbolic universe used to canonize symbolic expressions
	 * @param muMap
	 *            the map used to flyweight memory units
	 */
	void makeCanonic(SymbolicUniverse universe,
			Map<ImmutableMemoryUnit, ImmutableMemoryUnit> muMap) {
		List<MemoryUnit> list = new ArrayList<>(this.memUnits);

		// int numMu = this.memUnits.size();
		assert !this.canonic;
		// for (int i = 0; i < numMu; i++) {
		// ImmutableMemoryUnit mu = (ImmutableMemoryUnit) memUnits.get(i);
		for (int i = 0; i < list.size(); i++) {
			ImmutableMemoryUnit imu = (ImmutableMemoryUnit) list.get(i);

			assert imu != null;
			if (!imu.isCanonic())
				// memUnits.remove(imu);
				// memUnits.add(canonic(universe, imu, muMap));
				list.set(i, canonic(universe, imu, muMap));
		}
		this.memUnits = new HashSet<>(list);
		// for (MemoryUnit mu : list) {
		// ImmutableMemoryUnit imu = (ImmutableMemoryUnit) mu;
		//
		// assert mu != null;
		// if (!imu.isCanonic())
		// memUnits.remove(imu);
		// memUnits.add(canonic(universe, imu, muMap));
		// // memUnits.set(i, canonic(universe, mu, muMap));
		// }
		this.canonic = true;
	}

	/**
	 * Is this memory unit set canonic?
	 * 
	 * @return true iff this is canonic
	 */
	boolean isCanonic() {
		return this.canonic;
	}

	/**
	 * Implements the flyweight pattern for ImmutableMemoryUnit: if there
	 * already exists a memory unit which is equivalent to the given one, return
	 * that one, otherwise, add the memory unit to the map and return it.
	 * 
	 * This method goes into the memory unit and replaces each individual
	 * symbolic expression with the canonic version of that symbolic expression.
	 * 
	 * @param mu
	 *            the memory unit to be flyweighted
	 * @param muMap
	 *            the map to use for flyweighting in which the key-value pairs
	 *            have the form (X,X) for all canonic objects X
	 * @param universe
	 *            the symbolic universe to be used for canonicalizing symbolic
	 *            expressions
	 * @return the unique representative of the memory unit's equivalence class
	 */
	private ImmutableMemoryUnit canonic(SymbolicUniverse universe,
			ImmutableMemoryUnit mu,
			Map<ImmutableMemoryUnit, ImmutableMemoryUnit> muMap) {
		ImmutableMemoryUnit canonicMu = muMap.get(mu);

		if (canonicMu == null) {
			mu.makeCanonic(universe);
			muMap.put(mu, mu);
			return mu;
		}
		return canonicMu;
	}

	@Override
	public Iterable<MemoryUnit> memoryUnits() {
		return this.memUnits;
	}

	@Override
	public void add(MemoryUnit mu) {
		this.memUnits.add(mu);
	}

	@Override
	public void print(PrintStream out) {
		int i = 0;

		out.print("{");
		for (MemoryUnit mu : memUnits) {
			if (i != 0)
				out.print(", ");
			mu.print(out);
			i++;
		}
		out.print("}");
	}

	@Override
	public String toString() {
		StringBuffer result = new StringBuffer();
		int i = 0;

		result.append("{");
		for (MemoryUnit mu : memUnits) {
			if (i != 0)
				result.append(", ");
			result.append(mu);
			i++;
		}
		result.append("}");
		return result.toString();
	}
	
	// @Override
	// public int hashCode(){}
	
}
