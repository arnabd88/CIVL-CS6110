package edu.udel.cis.vsl.abc.ast.entity.IF;

import java.io.PrintStream;
import java.util.Iterator;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.token.IF.UnsourcedException;

/**
 * <p>
 * A lexical (static) scope in a translation unit. The C11 Standard specifies 4
 * kinds of scopes: FILE, BLOCK, FUNCTION, and FUNCTION_PROTOTYPE.
 * </p>
 * 
 * <p>
 * A scope contains declarations of various kinds of entities. An "entity" is
 * any conceptual thing which can be named using an identifier. An entity may be
 * declared in more than one scope (though the process of "linkage").
 * </p>
 * 
 * <p>
 * Global declarations are in the FILE scope. A BLOCK scope corresponds to a
 * block. The BLOCK scope corresponding to a function body includes the formal
 * parameters as well as the outermost local parameters. The only entities with
 * FUNCTION scope are (standard) labels---the labels that can be used as a
 * target of a "goto" statement. A FUNCTION_PROTOTYPE scope occurs only in a
 * function prototype, i.e., a function delcaration without body; such a scope
 * extends to the end of the declarator for the function prototype.
 * </p>
 * 
 * <p>
 * The set of all scopes in a translation unit forms a tree. The root of the
 * tree is the FILE scope.
 * </p>
 * 
 * <p>
 * There are four kinds of name spaces in a scope: (1) the label namespace,
 * which consists of all the (standard) label names in the scope; (2) the tag
 * namespace, which consists of all the tags used in struct, union, and
 * enumeration definitions; (3) the "member" namespaces (one namespace for each
 * struct or union containing the field names for that struct or union); and (4)
 * the namespace for "ordinary identifiers"---those declared in an ordinary (not
 * struct or union) declarator, or as an enumeration constant---, this includes
 * typedef names, variables, and functions. For example, the same identifier "X"
 * could be used to denote a label, the tag of a struct, a member of that
 * struct, and a variable, all in the same scope. However, "X" could not denote
 * both a variable and a function in the same scope; nor could it denote both a
 * struct tag and an enumeration tag in the same scope; but two different
 * structs in the same scope can both have a field named "X".
 * </p>
 * 
 * <p>
 * Ordinary entities include: functions, variables (that are not fields),
 * enumeration constants, and typedefs.
 * </p>
 * 
 * <p>
 * Note that "label" means standard label: the kind that is specified by an
 * identifier followed by a colon. Not a "case label" (CASE followed by a
 * constant expression then colon, used in switch statements), and not the
 * "default" label (also used in switch statements).
 * </p>
 * 
 * <p>
 * Note: Entities can have no name. It is OK if two distinct entities have no
 * name; they are not the same entity. It is as if each is given a new name
 * distinct from all other names.
 * </p>
 */
public interface Scope {

	/**
	 * These are the four different kinds of scopes.
	 */
	public enum ScopeKind {
		/**
		 * File scope. This is the root scope.
		 */
		FILE,
		/**
		 * A block scope.
		 */
		BLOCK,
		/**
		 * A function scope.
		 */
		FUNCTION,
		/**
		 * A function prototype scope.
		 */
		FUNCTION_PROTOTYPE,
		/**
		 * The scope for a CIVL-C contract. The contract scope contains the
		 * scope of the function signature and body.
		 */
		CONTRACT
	};

	// information about this scope in the scope tree...

	/**
	 * Returns the kind of scope this is.
	 * 
	 * @return the scope kind
	 * */
	ScopeKind getScopeKind();

	/**
	 * Returns the ID number of this scope, unique among the scope of its
	 * translation unit.
	 * 
	 * @return the scope ID
	 */
	int getId();

	/**
	 * Sets the ID number of this scope, which should be unique among the ID
	 * numbers of the scopes of its translation unit.
	 * 
	 * @param id
	 *            value to which ID number will be set
	 */
	void setId(int id);

	/**
	 * Returns the AST to which this scope belongs.
	 * 
	 * @return the AST to which this scope belongs
	 * */
	AST getAST();

	/**
	 * The parent scope, i.e., the scope directly containing this one. Null if
	 * this is the root scope.
	 * 
	 * @return the parent scope
	 */
	Scope getParentScope();

	/**
	 * The number of children of this scope in the scope tree.
	 * 
	 * @return the number of children scopes of this scope
	 */
	int getNumChildrenScopes();

	/**
	 * Returns the child scope of this scope, indexed from 0.
	 * 
	 * @param index
	 *            integer between 0 and numChildrenScope-1, inclusive
	 * @return child scope number index
	 * @exception IllegalArgumentException
	 *                if index is out of bounds
	 */
	Scope getChildScope(int index);

	/**
	 * Returns an iterator over the children scope of this scope.
	 * 
	 * @return an iterator over all children scopes
	 */
	Iterator<Scope> getChildrenScopes();

	/**
	 * Returns the depth of this scope as a node in the scope tree. The FILE
	 * scope has depth 0. Its immediate children have depth 1. Etc.
	 * 
	 * @return depth of this scope as node in scope tree
	 */
	int getScopeDepth();

	// Ordinary entities...

	/**
	 * Gets the set of all ordinary entities declared in this scope, represented
	 * as an iterable object.
	 * 
	 * @return iterable over all ordinary entities declared in this scope
	 */
	Iterable<OrdinaryEntity> getOrdinaryEntities();

	/**
	 * Adds an ordinary entity to this scope's collection of entities.
	 * 
	 * @param entity
	 *            an ordinary entity to be added to this scope
	 * @return the number of ordinary entities beloning to this scope before the
	 *         new one was added; this number becomes the index of the ordinary
	 *         entity
	 * @throws UnsourcedException
	 *             if the entity cannot be added to this scope for some reason,
	 *             for example, because there is already an ordinary entity with
	 *             that name in this scope
	 */
	int add(OrdinaryEntity entity) throws UnsourcedException;

	/**
	 * Gets the ordinary entity (variable/function/enumeration constant/typedef)
	 * in this scope with the given name, or <code>null</code> if there is not
	 * one. This does not look in ancestor or descendant scopes.
	 * 
	 * @param isType
	 *            true iff this is to get an entity of typedef; if false then
	 *            the first entity from the bottom of the scope is returned,
	 *            regardless of whether it is typedef or not
	 * @param name
	 *            the name of the ordinary entity
	 * @return the ordinary entity in this scope with that name or
	 *         <code>null</code> if none exists
	 */
	OrdinaryEntity getOrdinaryEntity(boolean isType, String name);

	/**
	 * Performs search for ordinary entity with given name using lexical
	 * scoping: if entity is not found in this scope, search the parent scope,
	 * etc. Returns first occurrence of ordinary entity with this name,
	 * searching in that order. If not found all the way up the scopes, returns
	 * <code>null</code>.
	 * 
	 * @param isType
	 *            true iff this is to get an entity of typedef; if false then
	 *            the first entity from the bottom of the scope is returned,
	 *            regardless of whether it is typedef or not
	 * @param name
	 *            name of the entity
	 * @return the first ordinary entity encountered with given name looking up
	 *         the scope tree, or <code>null</code>
	 */
	OrdinaryEntity getLexicalOrdinaryEntity(boolean isType, String name);

	/**
	 * Returns the number of variables declared in this scope. The set of
	 * variables is a subset of the set of entities. Variables include global
	 * variables, local variables declared in any block scope, including formal
	 * parameters to a function. They do not include members of structures or
	 * unions (aka "fields"). They do not include enumeration constants.
	 * 
	 * Note this does not include variables in ancestors or descendants of this
	 * scope.
	 * 
	 * @return the number of variables declared in this scope
	 */
	int getNumVariables();

	/**
	 * 
	 * The variables in this scope are assigned variable ID numbers 0, 1, 2,
	 * ..., at completion time. This method returns the variable with the given
	 * ID. Note that the variable ID is not necessarily the same as the entity
	 * ID.
	 * 
	 * @return the index-th variable in this scope, indexed from 0
	 */
	Variable getVariable(int index);

	/**
	 * Returns an iterator over the variables in this scope, in order of
	 * increasing variable ID.
	 * 
	 * @return an iterable over the variables in this scope.
	 */
	Iterable<Variable> getVariables();

	/**
	 * Returns the number of functions in this scope. Note this does not include
	 * functions in ancestors of this scope. The functions are of course a
	 * subset of the set of Entities.
	 * 
	 * @return the number of functions in this scope
	 */
	int getNumFunctions();

	/**
	 * The functions in this scope are assigned ID numbers 0, 1, 2, ..., at
	 * completion time. This method returns the function with the given index.
	 * 
	 * @return the index-th function in this scope, counting from 0
	 */
	Function getFunction(int index);

	/**
	 * Returns an iterator over the functions defined in this scope, in order of
	 * increasing function index.
	 * 
	 * @return iterator over functions in this scope
	 */
	Iterable<Function> getFunctions();

	// Tagged entities (enumerations, structures, and unions)...

	/**
	 * Gets the set of all tagged entities declared in this scope, represented
	 * as an iterable object.
	 * 
	 * @return iterable over all tagged entities declared in this scope
	 */
	Iterable<TaggedEntity> getTaggedEntities();

	/**
	 * Adds a tagged entity (an enumeration, structure, or union) to this scope.
	 * Tagged entities occupy a separate name space from ordinary entities.
	 * 
	 * @param entity
	 *            a tagged entity
	 * @return the number of tagged entities belonging to this scope before the
	 *         new one was added; this number is the index of the newly added
	 *         tagged entity in the tagged entity list
	 * @throws SyntaxException
	 *             if the entity cannot be added to this scope for some reason,
	 *             for example, because there is already a tagged entity with
	 *             the same name in this scope
	 */
	int add(TaggedEntity entity) throws SyntaxException;

	/**
	 * <p>
	 * Gets the tagged entity (struct/union/enumeration) in this scope with the
	 * given tag, or null if there is not one. This does not look in parent or
	 * descendant scopes.
	 * </p>
	 * 
	 * <p>
	 * Once you get the tagged entity, you can get its member entities
	 * (enumeration constants or fields). Those member entities are also part of
	 * this scope. The enumeration constants share the same name space as
	 * ordinary identifiers in this scope, but the fields are in their own
	 * entity-specific namespace.
	 * </p>
	 * 
	 * @param tag
	 *            the tag
	 * @return the tagged entity in this scope with that name or null if none
	 *         exists
	 */
	TaggedEntity getTaggedEntity(String tag);

	/**
	 * Performs search for struct/union/enumeration entity with given tag using
	 * lexical scoping: if entity is not found in this scope, search the parent
	 * scope, etc. Returns first occurrence of entity with this tag, searching
	 * in that order. If not found in any ancestor, returns <code>null</code>.
	 * 
	 * @return the first tagged entity encountered with the given tag, lookin up
	 *         the scope tree
	 */
	TaggedEntity getLexicalTaggedEntity(String tag);

	// Labels...

	/**
	 * Adds the given label to the list of labels occurring in this scope.
	 * 
	 * @param label
	 *            a label
	 * @return the number of labels belonging to this scope before the new one
	 *         was added; this is the index of the new label in the list of
	 *         labels
	 * @throws UnsourcedException
	 *             if the label cannot be added for some reasons, for example,
	 *             because there is already a label with the same name
	 */
	int add(Label label) throws UnsourcedException;

	/**
	 * Does the given label already belong to this scope?
	 * 
	 * @param label
	 *            a label
	 * @return <code>true</code> iff the list of labels belonging to this scope
	 *         contains the given label
	 */
	boolean contains(Label label);

	/**
	 * Gets the label declared in this scope with the given name. Labels only
	 * exist in a FUNCTION scope. A Label is an entity.
	 * 
	 * @param name
	 *            the label name
	 * @return the label in this scope with that name or <code>null</code> if
	 *         none exists
	 */
	Label getLabel(String name);

	/**
	 * Finds the label with the given name in this or any ancestor scope.
	 * 
	 * @param name
	 *            label name
	 * @return label with name or null
	 */
	Label getLexicalLabel(String name);

	/**
	 * Returns iterator over all (standard) labels declared in this scope.
	 * 
	 * @return iterator over all standard labels declared in this scope
	 */
	Iterator<Label> getLabels();

	/**
	 * Returns the number of (standard) labels declared in this scope.
	 * 
	 * @return number of labels in this scope
	 */
	int getNumLabels();

	/**
	 * Gets the label with the given label ID.
	 * 
	 * @param labelId
	 *            the label's id
	 * @return the label with the given id
	 * @exception IllegalArgumentException
	 *                if the labelId is less than 0 or greater than or equal to
	 *                the number of labels in this scope
	 */
	Label getLabel(int labelId);

	/**
	 * Prints complete description of this scope, with each line preceded by the
	 * string prefix.
	 * 
	 * @param prefix
	 *            any string
	 * @param out
	 *            PrintStream to which output is directed
	 */
	void print(String prefix, PrintStream out);

	/**
	 * Prints complete description of this scope.
	 * 
	 * @param out
	 *            PrintStream to which output is directed
	 */
	void print(PrintStream out);

	/**
	 * Determines whether this scope is equal to or a descendant of the given
	 * scope. This mean either this == that or the parent of this is a
	 * descendant of that.
	 * 
	 * @param that
	 *            another scope, not null
	 * @return true iff this scope is a descendant (or equal to) that scope
	 */
	boolean isDescendantOf(Scope that);

}
