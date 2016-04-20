package edu.udel.cis.vsl.abc.program.common;

import java.util.ArrayList;
import java.util.Map;

import edu.udel.cis.vsl.abc.ast.entity.IF.Entity;
import edu.udel.cis.vsl.abc.ast.entity.IF.OrdinaryEntity;
import edu.udel.cis.vsl.abc.ast.entity.IF.ProgramEntity;
import edu.udel.cis.vsl.abc.ast.entity.IF.Typedef;
import edu.udel.cis.vsl.abc.ast.node.IF.type.EnumerationTypeNode;
import edu.udel.cis.vsl.abc.ast.type.IF.EnumerationType;
import edu.udel.cis.vsl.abc.ast.type.IF.Enumerator;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.ast.type.IF.Type.TypeKind;
import edu.udel.cis.vsl.abc.util.IF.Pair;

/**
 * <p>
 * Records information about a set of ordinary entities from different
 * translation units that have the same name. Ordinary entities have names in
 * the ordinary name space; this includes variables, functions, typedefs, and
 * enumerators, but not the tags used to name structs, unions, and enumerations.
 * </p>
 * 
 * <p>
 * All of the entities must exist in the file scope of the translation unit.
 * Also, at most one entity can be associated to each translation unit (since
 * there is at most one entity in that unit's global scope ordinary namespace
 * with a given name).
 * </p>
 * 
 * @author siegel
 * 
 */
public class OrdinaryEntityInfo extends EntityInfo {

	/**
	 * The entities with external linkage. This is a list of translation unit
	 * ID-entity pairs.
	 */
	private ArrayList<Pair<Integer, OrdinaryEntity>> externals = new ArrayList<>();

	/**
	 * The entities with internal or no linkage. This is a list of translation
	 * unit ID-entity pairs.
	 */
	private ArrayList<Pair<Integer, OrdinaryEntity>> internals = new ArrayList<>();

	/**
	 * Constructs new info object with given name (which will be the name of all
	 * the entities associated to this object).
	 * 
	 * @param name
	 *            the name of entities
	 * @param numTranslationUnits
	 *            the total number of translation units in the system being
	 *            analyzed (not all of these necessarily have an entity with
	 *            this name)
	 */
	public OrdinaryEntityInfo(String name, int numTranslationUnits) {
		super(name, numTranslationUnits);
	}

	@Override
	protected void addEntity(int tuid, ProgramEntity entity) {
		ProgramEntity.LinkageKind kind = entity.getLinkage();
		Pair<Integer, OrdinaryEntity> pair = new Pair<>(tuid,
				(OrdinaryEntity) entity);

		if (kind == ProgramEntity.LinkageKind.EXTERNAL)
			externals.add(pair);
		else
			internals.add(pair);
	}

	/**
	 * <p>
	 * Is it the case that all of the entities are typedefs to types that are
	 * all compatible with each other? If so, you only need one typedef.
	 * </p>
	 * 
	 * <p>
	 * Note that the result returned by this method may change if the types are
	 * changed. This could happen if an incomplete tagged type is completed, for
	 * example. That could happen if an incomplete type is deemed to be
	 * equivalent to a complete one in another translation and merged with it.
	 * Hence it is recommended that First, complete all tagged types that are
	 * incomplete but are deemed to be consistent. Do that before doing this.
	 * </p>
	 * 
	 * 
	 * @return <code>true</code> iff all of the entities associated to this info
	 *         object are typedefs for equivalent types
	 */
	private boolean areEquivTypedefs() {
		if (!externals.isEmpty())
			return false;

		int n = internals.size();

		if (n == 0)
			return false;

		Pair<Integer, OrdinaryEntity> first = internals.get(0);
		Entity entity0 = first.right;

		if (!(entity0 instanceof Typedef))
			return false;

		Type type0 = ((Typedef) entity0).getType();

		for (int i = 1; i < n; i++) {
			Pair<Integer, OrdinaryEntity> pair = internals.get(i);
			Entity entity = pair.right;

			if (!(entity instanceof Typedef))
				return false;

			Type type = ((Typedef) entity).getType();

			if (!(type0.equivalentTo(type)))
				return false;
		}
		return true;
	}

	// if all of these are enumerators from same
	// complete enumeration class, nothing to do.
	// Otherwise:

	// get entity e_i. if e_i is an enumerator,
	// get its enumeration E.
	// Get the rep tuid j of the class
	// containing i in E; rename to newName(j). Else, rename to
	// newName(i).

	/**
	 * Returns an array of length internals.size(); in position i will be the
	 * new ID number to associate to the entity internals[i]. The new ID number
	 * will be used to issue a new name to the entity. The exception is if all
	 * are assigned the same ID number, then there is no need to rename
	 * anything.
	 * 
	 * @param enumMergeMap
	 *            a map detailing which enumeration types have been merged.
	 *            Read, not modified, by this method
	 * 
	 * @return array giving new ID number for each entity internals[i]
	 */
	private int[] computeNewIDs(Map<EnumerationType, Integer> enumMergeMap) {
		int numInternals = internals.size();
		int[] newIDs = new int[numInternals];

		for (int i = 0; i < numInternals; i++) {
			Pair<Integer, OrdinaryEntity> pair = internals.get(i);
			OrdinaryEntity entity = pair.right;

			if (entity instanceof Enumerator) {
				EnumerationType enumeration = ((Enumerator) entity).getType();
				int newID = enumMergeMap.get(enumeration);

				newIDs[i] = newID;
			} else {
				newIDs[i] = i;
			}
		}
		return newIDs;
	}

	private boolean isConstant(int[] array) {
		int length = array.length;

		if (length > 0) {
			int first = array[0];

			for (int i = 1; i < length; i++)
				if (array[i] != first)
					return false;
		}
		return true;
	}

	public void computeTypedefRemovals(Plan[] plan,
			Map<EnumerationType, Integer> enumMergeMap) {
		if (getNumEntities() > 1) {
			int numInternals = internals.size();

			if (areEquivTypedefs()) {
				Pair<Integer, OrdinaryEntity> pair0 = internals.get(0);
				Typedef typedef0 = (Typedef) pair0.right;
				int tuid0 = pair0.left;

				for (int i = 1; i < numInternals; i++) {
					Pair<Integer, OrdinaryEntity> pair = internals.get(i);

					plan[pair.left].addEntityRemoveAction(pair.right);
				}
				if (typedef0.getType().kind() == TypeKind.ENUMERATION) {
					for (Pair<Integer, OrdinaryEntity> pair : internals) {
						Typedef typedef = (Typedef) pair.right;
						EnumerationTypeNode enumTypeNode = (EnumerationTypeNode) typedef
								.getDefinition().getTypeNode();
						EnumerationType enumeration = enumTypeNode.getType();

						enumMergeMap.put(enumeration, tuid0);
					}
				}
			}
		}
	}

	public void computeRenamings(Plan[] plan,
			Map<EnumerationType, Integer> enumMergeMap) {
		if (getNumEntities() > 1) {
			if (areEquivTypedefs()) {
				// already dealt with
			} else {
				// rename all internal instances to unique names...
				int[] newIDs = computeNewIDs(enumMergeMap);

				if (externals.isEmpty() && isConstant(newIDs)) {
					// no renaming necessary
				} else {
					int numInternals = internals.size();

					for (int i = 0; i < numInternals; i++) {
						Pair<Integer, OrdinaryEntity> pair = internals.get(i);
						int tuid = pair.left;

						plan[tuid].addRenameAction(pair.right,
								newName(newIDs[i]));
					}
				}
			}
		}
	}
}
