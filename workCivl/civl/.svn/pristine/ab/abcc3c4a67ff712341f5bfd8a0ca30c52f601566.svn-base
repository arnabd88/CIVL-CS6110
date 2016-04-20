package edu.udel.cis.vsl.civl.state.persistent;

import java.io.PrintStream;
import java.util.Map;

import com.github.krukow.clj_ds.PersistentVector;

import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;

/**
 * A vector of process states. This is one of the two main components of the
 * state of a CIVL model (the other being the dynamic scope tree).
 * 
 * @author siegel
 * 
 */
public class ProcStateVector extends CIVLVector<PersistentProcessState> {

	/************************* Static Fields *************************/

	private final static int classCode = ProcStateVector.class.hashCode();

	/************************ Instance Fields ************************/

	/************************** Constructors *************************/

	ProcStateVector(PersistentVector<PersistentProcessState> processStates) {
		super(processStates);
	}

	ProcStateVector() {
		super();
	}

	/******************** Package-private Methods ********************/

	void print(PrintStream out, String prefix) {
		int numProcs = size();

		out.println(prefix + "Process states");
		for (int i = 0; i < numProcs; i++) {
			PersistentProcessState processState = get(i);

			if (processState == null)
				out.println(prefix + "| process " + i + ": null");
			else
				processState.print(out, prefix + "| ");
		}
	}

	ProcStateVector renumberScopes(int[] oldToNew) {
		int size = size();
		PersistentVector<PersistentProcessState> newVector = values;

		for (int i = 0; i < size; i++) {
			PersistentProcessState processState = values.get(i);
			PersistentProcessState newProcessState = processState
					.renumberScopes(oldToNew);

			if (newProcessState != processState)
				newVector = newVector.plusN(i, newProcessState);
		}
		return newVector == values ? this : new ProcStateVector(newVector);
	}

	ProcStateVector push(int pid, PersistentStackEntry entry) {
		return new ProcStateVector(values.plusN(pid, values.get(pid)
				.push(entry)));
	}

	/******************** Methods from CIVLVector ********************/

	@Override
	protected int computeHashCode() {
		return classCode ^ super.computeHashCode();
	}

	@Override
	protected boolean computeEquals(PersistentObject that) {
		return that instanceof ProcStateVector && super.computeEquals(that);
	}

	@Override
	protected ProcStateVector newVector(
			PersistentVector<PersistentProcessState> values) {
		return new ProcStateVector(values);
	}

	/***************** Methods from PersistentObject *****************/

	@Override
	protected void canonizeChildren(SymbolicUniverse universe,
			Map<PersistentObject, PersistentObject> canonicMap) {
		int size = values.size();

		for (int i = 0; i < size; i++) {
			PersistentProcessState processState = values.get(i);

			if (!processState.isCanonic())
				values = values.plusN(i,
						processState.canonize(universe, canonicMap));
		}
	}

	@Override
	protected ProcStateVector canonize(SymbolicUniverse universe,
			Map<PersistentObject, PersistentObject> canonicMap) {
		return (ProcStateVector) super.canonize(universe, canonicMap);
	}

	/************************ Public Methods *************************/

	// public ProcStateVector set(int index, PersistentProcessState
	// processState) {
	//
	// PersistentVector<PersistentProcessState> newVector = setVector(index,
	// processState);
	//
	// return newVector == values ? this : new ProcStateVector(newVector);
	// }

	@Override
	public ProcStateVector remove(int index) {
		PersistentVector<PersistentProcessState> newValues = values;
		int n = values.size() - 1;

		for (int i = index; i < n; i++) {
			PersistentProcessState procState = values.get(i + 1);

			procState = procState.setPid(i);
			newValues = newValues.plusN(i, procState);
		}
		newValues = newValues.minus();
		return new ProcStateVector(newValues);
	}

}
