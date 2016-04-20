package edu.udel.cis.vsl.abc.program.common;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;

import edu.udel.cis.vsl.abc.ast.entity.IF.ProgramEntity;
import edu.udel.cis.vsl.abc.ast.entity.IF.TaggedEntity;

/**
 * A plan on how to transform an AST to prepare it for merging.
 * 
 * @author siegel
 * 
 */
public class Plan {

	/**
	 * The set of entities in the translation unit whose definitions should be
	 * nullified.
	 */
	private Collection<TaggedEntity> defDeleteSet = new LinkedList<>();

	/**
	 * Mapping from entity that must be renamed to its new name.
	 */
	private Map<ProgramEntity, String> renameMap = new HashMap<>();

	/**
	 * Entities whose declarations should be deleted from the AST.
	 */
	private Collection<ProgramEntity> entityRemoveSet = new LinkedList<>();

	public Plan() {
	}

	public void addMakeIncompleteAction(TaggedEntity entity) {

		// System.out.println("Adding incompletion action for " + entity
		// + " def: " + entity.getDefinition());
		// System.out.flush();

		defDeleteSet.add(entity);
	}

	public void addRenameAction(ProgramEntity entity, String newName) {

		// System.out.println("Adding rename action for " + entity + " def: "
		// + entity.getDefinition() + " new name " + newName);
		// System.out.flush();

		renameMap.put(entity, newName);
	}

	public void addEntityRemoveAction(ProgramEntity entity) {

		// System.out.println("Adding removal action for " + entity + " def: "
		// + entity.getDefinition());
		// System.out.flush();

		entityRemoveSet.add(entity);
	}

	public Iterable<TaggedEntity> getMakeIncompleteActions() {
		return defDeleteSet;
	}

	public Map<ProgramEntity, String> getRenameMap() {
		return renameMap;
	}

	public Iterable<ProgramEntity> getEntityRemoveActions() {
		return entityRemoveSet;
	}

}
