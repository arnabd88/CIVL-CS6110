package edu.udel.cis.vsl.abc.ast.entity.IF;

import java.util.Enumeration;

import edu.udel.cis.vsl.abc.ast.node.IF.declaration.DeclarationNode;
import edu.udel.cis.vsl.abc.ast.type.IF.Enumerator;
import edu.udel.cis.vsl.abc.ast.type.IF.Field;
import edu.udel.cis.vsl.abc.front.common.astgen.PragmaHandler;

/**
 * <p>
 * An entity is an underlying program "conceptual thing" that can be named by an
 * identifier. The kinds of things include: variables, functions, typedefs,
 * structures, unions, enumerations, enumerators, fields, and labels.
 * </p>
 * 
 * <p>
 * An entity object has some list of declarations associated to it. It begins
 * with no declarations; a declaration is added using method
 * {@link #addDeclaration(DeclarationNode)}. There are also methods to get the
 * number of declarations and to get the i-th declaration.
 * </p>
 * 
 * @author siegel
 * 
 */
public interface Entity {

	/**
	 * The different kinds of Entity.
	 * 
	 */
	public static enum EntityKind {
		/**
		 * A variable: this is the static notion of variable. A variable is
		 * named thing that can store a value. Note that a single variable can
		 * be declared multiple times in C.
		 */
		VARIABLE,
		/**
		 * A function. A function is a thing that takes inputs, executes a
		 * statement and possibly returns a result. Note that a function can be
		 * declared multiple times in C, but should be defined at most once.
		 */
		FUNCTION,
		/**
		 * A typedef, the entity corresponding to an occurrence of
		 * <code>typedef</code> in the program. The typedef binds an identifier
		 * to a type.
		 */
		TYPEDEF,
		/**
		 * A structure or union, the entity corresponding to an occurrence of
		 * <code>struct</code> or <code>union</code> in the program.
		 */
		STRUCTURE_OR_UNION,
		/**
		 * An enumeration, the entity corresponding to an occurrence of an
		 * <code>enum</code> definition in a program. Note that an enumeration
		 * can be declared multiple times, but at most one instance can be
		 * complete, i.e., contain the curly brackets with the enumerator list.
		 */
		ENUMERATION,
		/**
		 * An enumerator, the identifier that occurs in the list inside an
		 * <code>enum</code> definition. An enumerator is an enumeration
		 * constant and in C has a constant integer value.
		 */
		ENUMERATOR,
		/**
		 * A field, the entity corresponding to a field declaration in the list
		 * inside a complete <code>struct</code> or <code>union</code>
		 * definition.
		 */
		FIELD,
		/**
		 * An ordinary label, which occurs in a labeled statement of the form
		 * <code>labelName : stmt</code>. (Note that neither the
		 * <code>case</code> nor <code>default</code> constructs in a
		 * <code>switch</code> statement generate an entity.)
		 */
		LABEL,
		/**
		 * A pragma domain, named by the first token following the
		 * <code># pragma</code> in a pragma. For example, all OpenMP pragmas
		 * begin <code># pragma omp</code>; the <code>omp</code> names an entity
		 * which is the OpenMP pragma domain. Each pragma domain may have a
		 * pragma handler which is used to process pragmas of its domain.
		 */
		PRAGMA_HANDLER,
		/**
		 * An ACSL behavior, named by the token between the keyword
		 * <code>behavior </code> and the symbol <code>:</code>.
		 */
		BEHAVIOR
	};

	/**
	 * <p>
	 * The kind of entity this is.
	 * </p>
	 * 
	 * <p>
	 * If the kind is {@link EntityKind#VARIABLE}, this entity may be safely
	 * cast to {@link Variable}
	 * </p>
	 * 
	 * <p>
	 * If the kind is {@link EntityKind#FUNCTION}, this entity may be safely
	 * cast to {@link Function}.
	 * </p>
	 * 
	 * <p>
	 * If the kind is {@link EntityKind#TYPEDEF}, this entity may be safely cast
	 * to {@link Typedef}.
	 * </p>
	 * 
	 * <p>
	 * If the kind is {@link EntityKind#STRUCTURE_OR_UNION}, this entity may be
	 * safely cast to {@link StructureOrUnion}.
	 * </p>
	 * 
	 * <p>
	 * If the kind is {@link EntityKind#ENUMERATION}, this entity may be safely
	 * cast to {@link Enumeration}.
	 * </p>
	 * 
	 * <p>
	 * If the kind is {@link EntityKind#ENUMERATOR}, this entity may be safely
	 * cast to {@link Enumerator}. An enumerator is an element of an
	 * enumeration.
	 * </p>
	 * 
	 * <p>
	 * If the kind is {@link EntityKind#FIELD}, this entity may be safely cast
	 * to {@link Field}. A "field" is a member of a structure or union.
	 * </p>
	 * 
	 * <p>
	 * If the kind is {@link EntityKind#LABEL}, this entity may be safely cast
	 * to {@link Label}.
	 * </p>
	 * 
	 * <p>
	 * If the kind is {@link EntityKind#PRAGMA_HANDLER}, this entity may be
	 * safely cast to {@link PragmaHandler}.
	 * </p>
	 * 
	 * @return the entity kind
	 */
	EntityKind getEntityKind();

	/**
	 * Gets the name of this entity. This is the identifier used in the
	 * declaration of the entity. It can be null in certain situations (e.g., an
	 * unnamed field).
	 * 
	 * @return the name of this entity
	 */
	String getName();

}
