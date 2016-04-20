package edu.udel.cis.vsl.abc.program.common;

import edu.udel.cis.vsl.abc.ast.entity.IF.Entity;
import edu.udel.cis.vsl.abc.ast.entity.IF.ProgramEntity;

/**
 * <p>
 * An EntityInfo object records information about a set of entities from
 * different translation units that share the same name. It then specifies the
 * actions that must be taken to transform the ASTs representing the translation
 * units before they can be merged into a single AST.
 * </p>
 * 
 * <p>
 * Suppose there are n translation units. Each translation unit can have at most
 * one file-scope tagged entity (for example) with the given tag. Similar
 * comment applies for the ordinary namespace (for functions, variables,
 * typedefs). Hence this info object will deal with at most n entities, and each
 * of those entities will come from a distinct translation unit.
 * </p>
 * 
 * <p>
 * The info object is created with "empty" information. It is built up by calls
 * to method {@link #add(int, Entity)}. Note that it is required that calls to
 * this method occur with increasing translation unit ID.
 * </p>
 * 
 * 
 * 
 * @author siegel
 * 
 */
public abstract class EntityInfo {

	// Fields...

	/**
	 * The total number of translation units in the system being analyzed. Not
	 * all of these will necessarily have an entity with this name.
	 */
	private int numTranslationUnits;

	/**
	 * The name of the entity, e.g., the variable name or function name for an
	 * ordinary entity, or the tag for a struct, union, or enum. This may be
	 * null: e.g., for an anonymous struct, union, or enum.
	 */
	private String name;

	/**
	 * The number of translation units that have an entity with this name in a
	 * particular namespace (ordinary or tagged).
	 */
	private int numEntities = 0;

	// Constructors...

	public EntityInfo(String name, int numTranslationUnits) {
		this.name = name;
		this.numTranslationUnits = numTranslationUnits;
	}

	// Supporting methods...

	protected String newName(int tuid) {
		return name + "$TU" + tuid;
	}

	// Abstract methods...

	/**
	 * Adds the given entity to this info object. The contract is the same as
	 * that of {@link #add(int, Entity)}. That method simply invokes this one
	 * and increments the counter that records the number of entities added.
	 * 
	 * @param tuid
	 *            the index of the translation unit to which the given entity
	 *            belongs
	 * @param entity
	 *            the entity to add
	 */
	protected abstract void addEntity(int tuid, ProgramEntity entity);

	// Public methods...

	/**
	 * Returns the number of entities added to this info object.
	 * 
	 * @return the number of entities added
	 */
	public int getNumEntities() {
		return numEntities;
	}

	/**
	 * Returns the (common) name of the entities controled by this info object.
	 * 
	 * @return the entity name
	 */
	public String getName() {
		return name;
	}

	/**
	 * Adds the given entity belonging to the specified translation unit to this
	 * info object.
	 * 
	 * Preconditions:
	 * <ul>
	 * <li>The entity must belong to the translation unit with index tuid.</li>
	 * <li>The entity must have name equal to the name specified when this
	 * object was created</li>
	 * <li>The additions must occur in the order of increasing tuid. I.e., in
	 * any two successive calls to this method on the same object, the tuid
	 * argument must increase.</li>
	 * </ul>
	 * 
	 * 
	 * @param tuid
	 *            index of translation unit to which the given entity belongs
	 * @param entity
	 *            a tagged entity with tag equal to the tag associated to this
	 *            info object
	 */
	public void add(int tuid, ProgramEntity entity) {
		addEntity(tuid, entity);
		numEntities++;
	}

	public int getNumTranslationUnits() {
		return numTranslationUnits;
	}

}
