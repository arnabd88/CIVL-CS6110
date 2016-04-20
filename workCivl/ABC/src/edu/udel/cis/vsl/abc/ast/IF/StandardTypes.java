package edu.udel.cis.vsl.abc.ast.IF;

import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.abc.ast.entity.IF.EntityFactory;
import edu.udel.cis.vsl.abc.ast.entity.IF.Scope;
import edu.udel.cis.vsl.abc.ast.entity.IF.Typedef;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.ast.type.IF.TypeFactory;
import edu.udel.cis.vsl.abc.token.IF.UnsourcedException;

/**
 * The class collects together the standard type definitions, e.g., size_t,
 * ptrdiff_t, etc. It provides methods to get the set of all names of these
 * types, to get the a list of artificially created typedefs for the types, and
 * to add those typedefs to a scope. The reason for all of this is to provide an
 * easy way to ignore typedefs in the standard header files and instead use the
 * symbolic versions of these types provided by the type factory.
 * 
 * @author siegel
 * 
 */
public class StandardTypes {

	private EntityFactory entityFactory;

	private TypeFactory typeFactory;

	private List<Typedef> standardTypedefs = new LinkedList<Typedef>();

	private HashSet<String> standardTypeNames = new HashSet<String>();

	public StandardTypes(EntityFactory entityFactory, TypeFactory typeFactory) {
		this.entityFactory = entityFactory;
		this.typeFactory = typeFactory;
		formLists();
	}

	private void add(String typeName, Type type) {
		Typedef typedef = entityFactory.newTypedef(typeName, type);

		typedef.setIsSystem(true);
		standardTypedefs.add(typedef);
		standardTypeNames.add(typeName);
	}

	private void formLists() {
		add("size_t", typeFactory.size_t());
		add("ptrdiff_t", typeFactory.ptrdiff_t());
		add("wchar_t", typeFactory.wchar_t());
		add("char16_t", typeFactory.char16_t());
		add("char32_t", typeFactory.char32_t());
		add("$proc", typeFactory.processType());
		add("$scope", typeFactory.scopeType());
		add("$memory", typeFactory.memoryType());
		// add("$heap", typeFactory.heapType());
	}

	/**
	 * Adds typdefs for all of the standard types to the given scope (usually
	 * the file scope). Each type name is defined to be the type returned by the
	 * type factory with the corresponding name.
	 * 
	 * @param scope
	 *            a static program scope
	 * @throws UnsourcedException
	 *             if any typedefs with same name are already in the scope
	 */
	public void addToScope(Scope scope) throws UnsourcedException {
		for (Typedef typedef : standardTypedefs)
			scope.add(typedef);
	}

	/**
	 * Returns the names as a collection.
	 * 
	 * @return set of names of standard types
	 */
	public Collection<String> getStandardTypeNames() {
		return standardTypeNames;
	}

	/**
	 * Returns the list of typedefs.
	 * 
	 * @return list of standard typedefs
	 */
	public List<Typedef> getStandardTypedefs() {
		return standardTypedefs;
	}

}
