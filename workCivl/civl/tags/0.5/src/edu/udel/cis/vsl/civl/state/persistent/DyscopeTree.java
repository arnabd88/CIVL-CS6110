package edu.udel.cis.vsl.civl.state.persistent;

import java.io.PrintStream;
import java.util.HashMap;
import java.util.Map;

import com.github.krukow.clj_ds.PersistentVector;
import com.github.krukow.clj_ds.Persistents;

import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * The dynamic scope tree. This is one of the two main components of the state
 * of a CIVL model. (The other is the call stack of each process.)
 * 
 * The dynamic scope tree consists of a set of dynamic scopes with the structure
 * of a rooted tree.
 * 
 * @author siegel
 * 
 */
public class DyscopeTree extends CIVLVector<PersistentDynamicScope> {

	/************************* Static Fields *************************/

	/**
	 * The hash code of this class, used in the hash code method to help
	 * distinguish hash codes of objects in this class from those in other
	 * classes. This can help because objects from different persistent classes
	 * will be mixed in the same hash data structures.
	 */
	private final static int classCode = DyscopeTree.class.hashCode();

	/************************** Constructors *************************/

	DyscopeTree(PersistentVector<PersistentDynamicScope> scopes) {
		super(scopes);
	}

	DyscopeTree() {
		super();
	}

	/******************** Package-private Methods ********************/

	/**
	 * Returns a dyscope tree obtained by renumbering the scopes in this tree
	 * according to the given map on dyscope ID numbers.
	 * 
	 * oldToNew maps the old dyscope IDs to the new IDs. The length of this map
	 * must be the number of dynamic scopes in this dyscope tree. A dyscope
	 * which is being removed will have its ID mapped to -1.
	 * 
	 * The following operations are performed:
	 * 
	 * Reorder the scopes. Some of the scopes may be removed.
	 * 
	 * Update the parent dyscope IDs in each scope.
	 * 
	 * Update the value vectors in each scope: since values may include scope
	 * references, those references need to be updated.
	 * 
	 * As usual, this method does not modify this dyscope tree. If any
	 * modifications are reuqired, a new dyscope tree is returned, a la the
	 * Immutable Pattern.
	 * 
	 * @param oldToNew
	 *            mapping of old dyscope IDs to new
	 * @return a dyscope tree with scopes renumbered as specified
	 */
	DyscopeTree renumberScopes(int[] oldToNew, ModelFactory modelFactory) {
		// TODO: do this in-place instead?
		SymbolicUniverse universe = modelFactory.universe();
		PersistentVector<PersistentDynamicScope> newVector = Persistents
				.vector();
		int size = size();
		Map<SymbolicExpression, SymbolicExpression> substitutionMap = new HashMap<>(
				size);

		assert size == oldToNew.length;
		for (int i = 0; i < size; i++) {
			int newId = oldToNew[i];

			if (newId != i) {
				SymbolicExpression oldValue = modelFactory.scopeValue(i);
				SymbolicExpression newValue = modelFactory.scopeValue(newId);

				substitutionMap.put(oldValue, newValue);
			}
		}
		for (int i = 0; i < size; i++) {
			int newId = oldToNew[i];

			if (newId >= 0) {
				PersistentDynamicScope scope = values.get(i);
				int parent = scope.getParent();

				if (parent >= 0) {
					parent = oldToNew[parent];
					assert parent >= 0;
				}
				scope = scope.setParent(parent);
				scope = scope.setValueVector(scope.getValueVector().substitute(
						substitutionMap, universe,
						scope.lexicalScope().variablesWithScoperefs()));
				if (newId < newVector.size())
					newVector = newVector.plusN(newId, scope);
				else {
					while (newId > newVector.size())
						newVector = newVector.plus(null);
					newVector = newVector.plus(scope);
				}
			}
		}
		return new DyscopeTree(newVector);
	}

	/**
	 * When a process is removed from the state, this method can be called to
	 * shift all process references in variable values and modify the reacher
	 * sets.
	 * 
	 * @param pid
	 *            pid of process being removed
	 * @param nprocs
	 *            the number of processes AFTER removing the one process
	 * @param modelFactory
	 *            factory used to produce process reference values and symbolic
	 *            universe
	 * @return new dynamic scope tree obtained from this one by replacing any
	 *         reference to process i for i>pid to a reference to process i-1; a
	 *         reference to process pid is replaced with an "undefined" value.
	 *         The "reacher" sets are also updated in the same way.
	 */
	DyscopeTree shiftProcReferences(int pid, int nprocs,
			ModelFactory modelFactory) {
		PersistentVector<PersistentDynamicScope> scopes = values;
		int numScopes = scopes.size();
		SymbolicUniverse universe = modelFactory.universe();
		Map<SymbolicExpression, SymbolicExpression> map = new HashMap<>(nprocs
				- pid + 1);

		// nprocs is the number of procs after removing one.
		// hence highest pid that can occur in state is nprocs.
		map.put(modelFactory.processValue(pid), modelFactory.processValue(-1));
		for (int i = pid + 1; i <= nprocs; i++)
			map.put(modelFactory.processValue(i),
					modelFactory.processValue(i - 1));

		for (int i = 0; i < numScopes; i++) {
			PersistentDynamicScope oldScope = values.get(i), newScope = oldScope
					.shiftProcReferences(pid, nprocs, map, universe);

			if (oldScope != newScope)
				scopes = scopes.plusN(i, newScope);
		}
		return scopes == values ? this : new DyscopeTree(scopes);
	}

	DyscopeTree setReachable(int sid, int pid) {
		return (DyscopeTree) set(sid, get(sid).setReachable(pid));
	}

	DyscopeTree unsetReachable(int sid, int pid) {
		return (DyscopeTree) set(sid, get(sid).unsetReachable(pid));
	}

	DyscopeTree simplify(Reasoner reasoner) {
		PersistentVector<PersistentDynamicScope> scopes = values;
		int numScopes = scopes.size();

		for (int i = 0; i < numScopes; i++) {
			PersistentDynamicScope oldScope = values.get(i), newScope = oldScope
					.simplify(reasoner);

			if (oldScope != newScope)
				scopes = scopes.plusN(i, newScope);
		}
		return scopes == values ? this : new DyscopeTree(scopes);

	}

	/****************** Methods from PersistentObject ****************/

	@Override
	protected void canonizeChildren(SymbolicUniverse universe,
			Map<PersistentObject, PersistentObject> canonicMap) {
		int size = values.size();

		for (int i = 0; i < size; i++) {
			PersistentDynamicScope scope = values.get(i);

			if (!scope.isCanonic())
				values = values.plusN(i, scope.canonize(universe, canonicMap));
		}
	}

	@Override
	protected DyscopeTree canonize(SymbolicUniverse universe,
			Map<PersistentObject, PersistentObject> canonicMap) {
		return (DyscopeTree) super.canonize(universe, canonicMap);
	}

	/********************* Methods from CIVLVector *******************/

	@Override
	protected int computeHashCode() {
		return classCode ^ super.computeHashCode();
	}

	@Override
	protected boolean computeEquals(PersistentObject obj) {
		return obj instanceof DyscopeTree && super.computeEquals(obj);
	}

	@Override
	protected DyscopeTree newVector(
			PersistentVector<PersistentDynamicScope> values) {
		return new DyscopeTree(values);
	}

	/********************** Other public methods *********************/

	public void print(PrintStream out, String prefix) {
		int numScopes = size();

		out.println(prefix + "Dynamic scopes");
		for (int i = 0; i < numScopes; i++) {
			PersistentDynamicScope scope = get(i);

			if (scope == null)
				out.println(prefix + "| scope " + i + ": null");
			else
				scope.print(out, "" + i, prefix + "| ");
		}
	}
}
