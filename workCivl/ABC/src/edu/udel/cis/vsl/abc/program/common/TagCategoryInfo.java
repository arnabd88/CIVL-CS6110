package edu.udel.cis.vsl.abc.program.common;

import java.util.ArrayList;
import java.util.Map;

import edu.udel.cis.vsl.abc.ast.entity.IF.TaggedEntity;
import edu.udel.cis.vsl.abc.ast.type.IF.EnumerationType;
import edu.udel.cis.vsl.abc.ast.type.IF.Enumerator;
import edu.udel.cis.vsl.abc.ast.type.IF.Field;
import edu.udel.cis.vsl.abc.ast.type.IF.StructureOrUnionType;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.err.IF.ABCRuntimeException;
import edu.udel.cis.vsl.abc.util.IF.Pair;

/**
 * Information on a set of entities with the same tag and kind (struct, enum, or
 * union) in different translation units.
 * 
 * Each {@link TagCategoryInfo} object deals with one particular category (kind)
 * of tagged entities: either struct, enum, or union.
 * 
 * @author siegel
 * 
 */
public class TagCategoryInfo {

	/**
	 * The parent entity of this which is a part. Each {@link TaggedEntityInfo}
	 * comprises three {@link TagCategoryInfo} objects: one each for enums,
	 * structs, and unions.
	 */
	private TaggedEntityInfo parent;

	/**
	 * The number of entities of this kind and with this tag.
	 */
	private int numEntities = 0;

	/**
	 * List of pairs (t,e), where t is the translation unit ID and e is an
	 * incomplete entity in that translation unit.
	 */
	private ArrayList<Pair<Integer, TaggedEntity>> incompletes = new ArrayList<>();

	private ArrayList<ArrayList<Pair<Integer, TaggedEntity>>> completeClasses = new ArrayList<>();

	TagCategoryInfo(TaggedEntityInfo parent) {
		this.parent = parent;
	}

	void add(Pair<Integer, TaggedEntity> pair) {
		TaggedEntity entity = pair.right;
		ArrayList<Pair<Integer, TaggedEntity>> theClass = null;

		if (entity.isComplete()) {
			Type entityType = entity.getType();

			for (ArrayList<Pair<Integer, TaggedEntity>> completeClass : completeClasses) {
				TaggedEntity representative = completeClass.get(0).right;

				if (representative.getType().equivalentTo(entityType)) {
					theClass = completeClass;
					break;
				}
			}
			if (theClass == null) {
				theClass = new ArrayList<>();
				completeClasses.add(theClass);
			}
		} else {
			theClass = incompletes;
		}
		theClass.add(pair);
		numEntities++;
	}

	int getNumEntities() {
		return numEntities;
	}

	boolean isEmpty() {
		return numEntities == 0;
	}

	boolean isConsistent() {
		return completeClasses.size() <= 1;
	}

	// it is possible for two complete classes to merge
	// because they use a sub-structure S and S is incomplete
	// in one but complete in the other, and then S becomes
	// complete everywhere.

	/**
	 * <p>
	 * In the case where there is a single complete class, this method completes
	 * the types of all incomplete types and moves all of them into the complete
	 * class.
	 * </p>
	 * 
	 * <p>
	 * Precondition: numCompleteClasses==1 && numIncompletes&ge;1.
	 * </p>
	 */
	private boolean fullyComplete() {
		if (completeClasses.size() == 1 && !incompletes.isEmpty()) {
			ArrayList<Pair<Integer, TaggedEntity>> completeClass = completeClasses
					.get(0);
			TaggedEntity completeEntity = getCompleteClassRepresentative(completeClass).right;

			for (Pair<Integer, TaggedEntity> pair : incompletes)
				complete(pair.right, completeEntity);
			// put everything into completeClass.
			completeClass.addAll(incompletes);
			incompletes.clear();
			return true;
		}
		return false;
	}

	boolean merge() {
		int numIncompletes = incompletes.size();
		int numCompleteClasses = completeClasses.size();

		if (numCompleteClasses == 0
				|| (numIncompletes == 0 && numCompleteClasses == 1))
			return false;
		if (numCompleteClasses == 1) {
			fullyComplete();
			return true;
		} else {
			completeClasses.clear();
			incompletes.clear();
			for (Pair<Integer, TaggedEntity> pair : parent.getEntityPairs())
				add(pair);
			fullyComplete();
			return numIncompletes != incompletes.size()
					|| numCompleteClasses != completeClasses.size();
		}
	}

	// you actually want to complete the incomplete type because
	// this type is shared by many other types, so the change
	// will be reflected in all types which use that type
	private void complete(TaggedEntity incomplete, TaggedEntity complete) {
		if (incomplete instanceof EnumerationType) {
			Iterable<Enumerator> iter = ((EnumerationType) complete)
					.getEnumerators();

			((EnumerationType) incomplete).complete(iter);
		} else if (incomplete instanceof StructureOrUnionType) {
			Iterable<Field> iter = ((StructureOrUnionType) complete)
					.getFields();

			((StructureOrUnionType) incomplete).complete(iter);
		}
	}

	/**
	 * Given a complete class (i.e., a list of entities from different
	 * translation units which will all have the same complete type), finds one
	 * member which is already complete and returns its translation unit ID.
	 * This is the "representative" of its class, and in the final merged AST,
	 * the definition from the representative translation unit only will be
	 * preserved.
	 */
	private Pair<Integer, TaggedEntity> getCompleteClassRepresentative(
			ArrayList<Pair<Integer, TaggedEntity>> completeClass) {
		for (Pair<Integer, TaggedEntity> pair : completeClass) {
			if (pair.right.getDefinition() != null)
				return pair;
		}
		throw new ABCRuntimeException(
				"Unreachable: there must be at least one really complete entity");
	}

	/**
	 * Returns the translation unit ID of one of the entities controled by this
	 * info object.
	 * 
	 * @return tuid of one entity
	 */
	private Pair<Integer, TaggedEntity> getOverallRepresentative() {
		if (completeClasses.isEmpty()) {
			if (incompletes.isEmpty())
				throw new ABCRuntimeException("unreachable");
			return incompletes.get(0);
		} else {
			return getCompleteClassRepresentative(completeClasses.get(0));
		}
	}

	/**
	 * For enumeration infos only, adds to map all (e,j), where e is a complete
	 * Enumeration entity and j is the tuid of the representative of the class
	 * containing e.
	 * 
	 * @param enumMergeMap
	 *            the map which will be modified by this method. Entries for the
	 *            form (e,j) will be added to this map.
	 */
	void addToEnumMergeMap(Map<EnumerationType, Integer> enumMergeMap) {
		for (ArrayList<Pair<Integer, TaggedEntity>> completeClass : completeClasses) {
			int representative = getCompleteClassRepresentative(completeClass).left;

			for (Pair<Integer, TaggedEntity> pair : completeClass) {
				enumMergeMap.put((EnumerationType) pair.right, representative);
			}
		}
	}

	/**
	 * <p>
	 * Computes the actions that need to be performed regarding this tag.
	 * </p>
	 * 
	 * <p>
	 * The first kind of actions are renaming actions. These are determined as
	 * follows. First, "exclusive" means that this tag is only used by one
	 * category (i.e., one of struct, union, enum). "Consistent" means that in
	 * this category, there is at most one complete class.
	 * <ul>
	 * <li>if exclusive:
	 * <ul>
	 * <li>if consistent, nothing to do</li>
	 * <li>if inconsistent, each complete class gets a representative name, and
	 * incompletes are left alone</li>
	 * </ul>
	 * </li>
	 * <li>if not exclusive:
	 * <ul>
	 * <li>if consistent, everything in this info gets renamed to a single new
	 * name</li>
	 * <li>if inconsistent, each complete class gets a representative name,
	 * incompletes get a single distinct representative name</li>
	 * </ul>
	 * </li>
	 * </ul>
	 * </p>
	 * 
	 * <p>
	 * The second category of actions are definition deletions. For each
	 * complete class, only one member gets to keep the complete definition of
	 * the entity; the others will be made incomplete.
	 * </p>
	 * 
	 * @param plans
	 *            array of plans to be updated, one for each AST
	 */
	void addActions(Plan[] plans) {
		if (isEmpty())
			return;

		boolean consistent = isConsistent();
		boolean exclusive = parent.isExclusive();

		// rename complete classes in inconsistent case, since this
		// is the same whether exclusive or not...
		if (!consistent) {
			for (ArrayList<Pair<Integer, TaggedEntity>> completeClass : completeClasses) {
				int representative = getCompleteClassRepresentative(completeClass).left;
				String newName = parent.newName(representative);

				for (Pair<Integer, TaggedEntity> pair : completeClass)
					plans[pair.left].addRenameAction(pair.right, newName);
			}
		}
		if (!exclusive) {
			if (consistent) {
				int representative = getOverallRepresentative().left;
				String newName = parent.newName(representative);

				for (Pair<Integer, TaggedEntity> pair : incompletes)
					plans[pair.left].addRenameAction(pair.right, newName);
				for (ArrayList<Pair<Integer, TaggedEntity>> completeClass : completeClasses) {
					for (Pair<Integer, TaggedEntity> pair : completeClass)
						plans[pair.left].addRenameAction(pair.right, newName);
				}
			} else {
				if (!incompletes.isEmpty()) {
					int representative = incompletes.get(0).left;
					String newName = parent.newName(representative);

					for (Pair<Integer, TaggedEntity> pair : incompletes)
						plans[pair.left].addRenameAction(pair.right, newName);
				}
			}
		}
		// add incompletion actions...
		for (ArrayList<Pair<Integer, TaggedEntity>> completeClass : completeClasses) {
			int representative = getCompleteClassRepresentative(completeClass).left;

			for (Pair<Integer, TaggedEntity> pair : completeClass) {
				int tuid = pair.left;

				if (tuid != representative) {
					TaggedEntity entity = pair.right;

					if (entity.getDefinition() != null)
						plans[tuid].addMakeIncompleteAction(entity);
				}
			}
		}
	}
}
